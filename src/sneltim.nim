#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, genasts, typetraits, sequtils, strutils, setutils, sets, tables, dom, options, enumerate]
import fusion/matching
export sets, tables, dom, sequtils

import ./private/[templhtml, utils]


type
  PatchRef[T] = ref object
    val: ref T
    prevVal: T
    patchProcs: seq[proc()]

func new[T](v: T): ref T =
  new result
  result[] = v

func newPatchRef[T](val: T): PatchRef[T] =
  new result
  result.val = new val

proc patch(pr: PatchRef, init = false) =
  if pr.val[] != pr.prevVal or init:
    debugEcho "patch: ", pr.val[]
    let l = len(pr.patchProcs)
    for i in 0 ..< l: pr.patchProcs[i]()
    pr.prevVal = pr.val[]


type
  # for some reason I cant use Members as typeclass for Components generic params
  Members = concept m
    m is ref object
    for f in m[].fields:
      f is PatchRef

  ComponentInstance[L,V] = object
    init: proc()
    mount: proc(parent: Node, getHook: proc: Node)  #TODO:  refactor for using getHook
    detach: proc()
    pubLetMembers: L
    pubVarMembers: V
    getFirstNode: proc: Node

  ComponentInstanceSeq[L,V] = object
    instances: seq[ComponentInstance[L,V]]
    getFirstNode: proc: Node

  ComponentInstanceTuple[L: static int] = concept t
    t is tuple
    for c in t.fields:
      c is ComponentInstance
    #L == tupleLen(t)  # not working 
  
  ComponentInstanceOptions[L: static int, T: ComponentInstanceTuple[L]] = object
    instances: T
    active: range[0 .. L-1]
    initialized: array[0 .. L-1, bool]

  Component*[L,V] = object
    create: proc: ComponentInstance[L,V]

template instanceType(c: Component): type =
  ComponentInstance[c.L, c.V]

template instanceSeqType(c: Component): type =
  ComponentInstanceSeq[c.L, c.V]

func newComponentInstanceOptions[T: ComponentInstanceTuple](L: static int, instances: T): ComponentInstanceOptions[L, T] =
  result = ComponentInstanceOptions[L, T](instances: instances)

let emptyComponent = Component[tuple[], tuple[]](
  create: proc: ComponentInstance[tuple[], tuple[]] =
    var getHook: proc: Node
    result.init = proc = discard
    result.mount = proc(_: Node, h: proc: Node) =
      getHook = h
    result.detach = proc = discard
    result.getFirstNode = proc: Node = getHook()
)


proc patch[M: Members](members: M, init = false) =
  for member in members[].fields:
    patch member, init

# used by the pred element to get its hook
proc getFirstNode*(node: Node): Node = node

proc getFirstNode*(options: ComponentInstanceOptions): Node =
  for i, instance in enumerate(options.instances.fields):
    if i == options.active:
      return getFirstNode(instance)


let
  templCodeBlocks {.compiletime.} = genSym(nskLabel, "templCodeBlocks")
  templCodeBlock  {.compiletime.} = genSym(nskLabel, "templCodeBlock")


proc setAttrProperly*(node: Node, attr: string, val: auto) =
  let val = cstring($val)
  case attr
  of "value": node.value = val
  else: node.setAttr(attr, val)



macro componentTyped(
  memberNames: static array[MemberKind, seq[string]],
  membersInherit: static Table[string, NimNode],
  templ: static Templ,
  body: typed
): untyped =

  # for capturing in nested procs
  let memberNames = memberNames
  var membersInherit = membersInherit

  let members = [
    priv:   genSym(nskLet, "privMembers"),
    pubLet: genSym(nskLet, "pubLetMembers"),
    pubVar: genSym(nskLet, "pubVarMembers"),
  ]

  var
    memberSyms: seq[NimNode]
    memberProcs: seq[NimNode]
    memberProcRefs: seq[seq[int]]   # procId  ->  referenced memberIds

  type UnpackMemberLvl = enum justUnbind, getMPatchRef, getMVal

  # generate member access (to either the PatchRef or actual value)
  proc unpackMember(kind: MemberKind, name: string, lvl = getMVal): NimNode =
    assert name in memberNames[kind]
    let members = members[kind]
    result = ident(name)
    if lvl != justUnbind:
      result = 
        if name in membersInherit: membersInherit[name]
        else:
          quote do: `members`.`result`
      if lvl == getMVal:
        result = quote do: `result`.val[]

  proc unbind(node: NimNode, lvl = getMVal, also: seq[NimNode] = @[]): NimNode =
    case node.kind
    of nnkSym:
      if node in memberSyms or node in also:
        let name = $node
        for kind, names in memberNames:
          if name in names:
            return unpackMember(kind, name, lvl)
        result = ident(name)

      elif node.symKind != nskLabel and
        (let T = node.getType; T.kind in {nnkSym, nnkIdent} and $T == $node):  # check if is typedesc (a bit hacky solution :/)
          result = ident($node)

      else:
        result = node

    of nnkHiddenAddr, nnkHiddenDeref:
      result = unbind(node[0], lvl, also)
    
    of nnkHiddenStdConv:
      result = unbind(node[1], lvl, also)
    
    of AtomicNodes - {nnkSym}:
      result = node
    
    else:
      result = node.kind.newTree()
      for node in node:
        result.add unbind(node, lvl, also)

  proc findMemberRefs(node: NimNode): seq[int] =
    case node.kind
    of nnkSym:
      if (let id = memberSyms.find(node); id >= 0):
        result &= id
      else:
        if (let id = memberProcs.find(node); id >= 0):
          result &= memberProcRefs[id]

    of nnkHiddenAddr, nnkHiddenDeref:
      result = findMemberRefs(node[0])

    of AtomicNodes - {nnkSym}: discard

    else:
      for child in node:
        result &= findMemberRefs(child)
      result = deduplicate(result)


  # --- build member type/init and collect member symbols, codeblocks: ---

  let
    membersTypes = [
      priv:   genSym(nskType, "PrivMembers"),
      pubLet: genSym(nskType, "PubLetMembers"),
      pubVar: genSym(nskType, "PubVarMembers"),
    ]

  var
    membersTypeFields, membersConstr: array[MemberKind, NimNode]
    templ = templ
    initCode = newStmtList()
    codeBlocksSection: NimNode

  for kind in MemberKind:
    membersTypeFields[kind] = nnkRecList.newTree()
    membersConstr[kind] = nnkObjConstr.newTree(membersTypes[kind])

  proc getMemberInfos(sym, val: NimNode): tuple[name: string, typeField, defaultVal: NimNode] =
    result.name = $sym
    let field = ident(result.name)
    let td = sym.getTypeInst.unbind
    result.typeField = nnkIdentDefs.newTree(
      field,
      nnkBracketExpr.newTree(bindSym"PatchRef", td),
      newNilLit()
    )
    result.defaultVal =
      if val.kind == nnkEmpty: newCall(bindSym"default", td)
      else: val.unbind

  proc addPubMemberInit(kind: range[pubLet..pubVar], name: string, defaultVal: NimNode) =
    membersConstr[kind].add nnkExprColonExpr.newTree(
      ident(name),
      newCall(bindSym"newPatchRef", defaultVal)
    )

  proc setMemberInherit(name: string, val: NimNode) =
    val.expectKind nnkDerefExpr
    val.expectLen 1
    val[0].expectKind nnkDotExpr
    val[0].expectLen 2
    val[0][1].expectKind {nnkSym, nnkIdent}
    assert $val[0][1] == "val"
    membersInherit[name] = val[0][0]
      
  proc scanBody(body: NimNode) =
    for stmt in body:
      case stmt.kind
      of nnkStmtList, nnkStmtListExpr: scanBody stmt

      of nnkVarSection:
        for def in stmt:
          for i, sym in def[0 ..< ^2]:
            memberSyms.add sym
            let (name, typeField, defaultVal) = getMemberInfos(sym, def[^1])

            if name in membersInherit:
              setMemberInherit(name, def[^1])

            elif name in memberNames[pubVar]:
              membersTypeFields[pubVar].add typeField
              addPubMemberInit(pubVar, name, defaultVal)
            elif name in memberNames[priv]:
              membersTypeFields[priv].add typeField
              let members = members[priv]
              let field = ident(name)
              initCode.add: quote do:
                `members`.`field` = newPatchRef(`defaultVal`)
            
            else: assert false

      of nnkLetSection:
        for def in stmt:
          for i, sym in def[0 ..< ^2]:
            let (name, typeField, defaultVal) = getMemberInfos(sym, def[^1])
            if name in membersInherit:
              memberSyms.add sym
              setMemberInherit(name, def[^1])
            if name in memberNames[pubLet]:
              memberSyms.add sym
              membersTypeFields[pubLet].add typeField
              addPubMemberInit(pubLet, name, defaultVal)
            else:
              initCode.add nnkLetSection.newTree(nnkIdentDefs.newTree(ident($sym), def[^2], def[^1]))

      of nnkProcDef, nnkFuncDef:
        memberProcRefs &= findMemberRefs(stmt)
        memberProcs &= stmt[0]
        initCode.add unbind(stmt)

      of nnkBlockStmt:
        if stmt[0] == templCodeBlocks:
          codeBlocksSection = stmt[1]
        else:
          initCode.add unbind(stmt)
        
      else: discard
      
  scanBody body

  # build members types
  proc buildMembersTypeDef(kind: MemberKind): NimNode =
    nnkTypeSection.newTree(nnkTypeDef.newTree(
      membersTypes[kind],
      newEmptyNode(),
      nnkRefTy.newTree(nnkObjectTy.newTree(
        newEmptyNode(),
        newEmptyNode(),
        membersTypeFields[kind]
      ))
    ))
  let pubMembersTypeDefs = newStmtList(
    buildMembersTypeDef(pubLet),
    buildMembersTypeDef(pubVar)
  )
  let privMembersTypeDef = buildMembersTypeDef(priv)

  # add member def to init code
  var initMembers = newStmtList()
  for kind, constr in membersConstr:
    let members = members[kind]
    initMembers.add: quote do:
      let `members` = `constr`

  # collect codeblocks
  var subComponentCodeBlocks: array[TemplElemControlFlowKinds, seq[NimNode]]
  proc collectCodeBlocks(node: NimNode) =
    for node in node:
      case node.kind
      of nnkStmtList, nnkStmtListExpr: collectCodeBlocks node
      of nnkDiscardStmt:               collectCodeBlocks node[0]

      of nnkBlockStmt, nnkBlockExpr:
        if node[0] == templCodeBlock:
          var codeBlock: CodeBlock
          let code = 
            if node[1].kind == nnkStmtList and len(node[1]) == 1: node[1][0]
            else: node[1]
          codeBlock.codeRaw = unbind(code, lvl=getMPatchRef)
          codeBlock.code    = unbind(code, lvl=getMVal)
          for memberId in findMemberRefs(code):
            let name = $memberSyms[memberId]
            for kind in MemberKind:
              if (let i = memberNames[kind].find(name); i >= 0):
                codeBlock.refs[kind] &= i
          templ.codeBlocks &= codeBlock

        else: collectCodeBlocks node[1]

      of nnkForStmt:
        subComponentCodeBlocks[templFor] &= unbind(node[^1], lvl=justUnbind, also=getForVars(node))

      of nnkIfStmt:
        for branch in node:
          subComponentCodeBlocks[templIf] &= unbind(
            branch[^1],
            lvl = justUnbind,
            also =
              if branch.kind == nnkElifBranch: getIfCondBindings(branch[0])
              else: @[]
          )

      of nnkLetSection:
        for defs in node:
          memberSyms &= defs[0 ..< ^2]

      else: discard

  collectCodeBlocks codeBlocksSection.denestStmtList

  # generate symbols for template elements
  for elem in templ.elems.mitems:
    elem.sym = genSym(nskVar, "elem")
    case elem.kind
    of templFor:
      elem.forComponent = genSym(nskLet, "forComponent")
    of templIf:
      for (_, _, component) in elem.elifBranches.mitems:
        component = genSym(nskLet, "elifBranchComponent")
      if Some((@body, _)) ?= elem.elseBody:
        elem.elseBody = some((body, genSym(nskLet, "elseComponent")))
    else: discard


  # --- generate instance: ---

  proc code(id: CodeBlockId): NimNode =
    templ.codeBlocks[id].code

  proc codeRaw(id: CodeBlockId): NimNode =
    templ.codeBlocks[id].codeRaw

  proc refs(id: CodeBlockId): array[MemberKind, seq[int]] =
    templ.codeBlocks[id].refs

  let
    rootParent = genSym(nskVar, "rootParent")
    getRootHook = genSym(nskVar, "getRootHook")

  proc parent(elem: TemplElem): NimNode =
    if elem.parentId >= 0: 
      templ.elems[elem.parentId].sym
    else: rootParent

  proc hook(elem: TemplElem): NimNode =
    if elem.hookId >= 0:
      templ.elems[elem.hookId].sym
    else: newCall(getRootHook)

  proc getHookProc(elem: TemplElem): NimNode =
    if elem.hookId >= 0:
      let sym = templ.elems[elem.hookId].sym
      quote do:
        proc: Node = `sym`.getFirstNode()
    else: getRootHook


  let patchAll = genSym(nskProc, "patchAll")
  let patchAllDef = block:
    var procBody = newStmtList()
    let initParam = genSym(nskParam, "init")
    for members in members:
      procBody.add: quote do:
        patch `members`, `initParam`
    quote do:
      proc `patchAll`(`initParam` = false) =
        `procBody`


  let defElems = block:
    var result, resultDefer = newStmtList()
    var nextSubCodeBlocksId: array[TemplElemControlFlowKinds, int]

    proc buildSubComponent(
      elem: TemplElem,
      kind: TemplElemControlFlowKinds,
      component: NimNode,
      body: Templ,
      newMembers: seq[NimNode]
    ): NimNode =

      var newMemberNames: array[MemberKind, seq[string]]
      var componentBody = newStmtList()

      for newMember in newMembers:
        assert newMember.kind == nnkSym
        let td = newMember.getTypeInst()
        let name = $newMember
        if td.kind == nnkVarTy:
          newMemberNames[pubVar].add name
          componentBody.add newVarStmt(
            ident(name),
            newCall(bindSym"default", unbind(td[0]))
          )
        else:
          let td =
            if td.kind == nnkBracketExpr and td[0].kind == nnkSym and $td[0] =~= "lent":
              td[1]
            else: td
          newMemberNames[pubLet].add name
          componentBody.add newLetStmt(
            ident(name),
            newCall(bindSym"default", unbind(td))
          )

      # inherit members
      var membersInheritDef = nnkTableConstr.newTree()
      for kind, memberNames in memberNames:
        for name in memberNames:
          if newMemberNames.allIt(name notin it):
            newMemberNames[kind] &= name
            membersInheritDef.add nnkExprColonExpr.newTree(newLit(name), newCall(bindSym"newEmptyNode"))
            let val = unpackMember(kind, name, getMVal)
            componentBody.add:
              if kind == pubLet: newLetStmt(ident(name), val)
              else:              newVarStmt(ident(name), val)

      let codeBlocks = subComponentCodeBlocks[kind][nextSubCodeBlocksId[kind]]
      componentBody.add: quote do:
        block `templCodeBlocks`:
          `codeBlocks`

      genAst(component, newMemberNames, membersInheritDef, templ = body.toAstGen, componentBody):
        let component = componentTyped(newMemberNames, toTable[string, NimNode](membersInheritDef), templ, componentBody)

    for elem in templ.elems:
      let sym = elem.sym
      case elem.kind
      of templText:
        result.add: quote do:
          var `sym` = document.createTextNode("")

      of templTag:
        let tag = elem.tag
        result.add: quote do:
          var `sym` = document.createElement(`tag`)

      of templComponent:
        let component = elem.component.code
        result.add: quote do:
          var `sym`: instanceType(`component`)

      of templFor:
        let component = elem.forComponent

        result.add: buildSubComponent(elem, templFor, component, elem.forBody, getForVars(elem.forHead.code))
        inc nextSubCodeBlocksId[templFor]

        result.add: quote do:
          var `sym`: instanceSeqType(`component`)

        let hook = elem.hook
        resultDefer.add: quote do:
          `sym`.getFirstNode = proc: Node =
            if len(`sym`.instances) > 0:
              `sym`.instances[0].getFirstNode()
            else:
              `hook`.getFirstNode()

      of templIf:
        var instances = nnkTupleConstr.newTree()

        for (cond, body, component) in elem.elifBranches:
          result.add buildSubComponent(elem, templIf, component, body, getIfCondBindings(cond.code))
          inc nextSubCodeBlocksId[templIf]
          instances.add: quote do:
            `component`.create()

        if Some((@body, @component)) ?= elem.elseBody:
          result.add buildSubComponent(elem, templIf, component, body, @[])
          inc nextSubCodeBlocksId[templIf]
          instances.add: quote do:
            `component`.create()
        else:
          instances.add: quote do:
            emptyComponent.create()

        let L = len(elem.elifBranches) + 1

        result.add: quote do:
          var `sym` = newComponentInstanceOptions(`L`, `instances`)


    result.add resultDefer
    result


  let getFirstNodeProc = block:
    let firstNode = templ.elems[0].sym
    quote do:
      proc: Node = `firstNode`.getFirstNode()


  let initProc = block:
    var procBody = newStmtList()

    template addPatch(id: CodeBlockId, body: untyped) =
      let refs = id.refs
      let code {.inject.} = id.code
      if refs.allIt(len(it) == 0):
        procBody.add: quote do:
          body
      else:
        let patchProc {.inject.} = genSym(nskProc, "patch")
        procBody.add: quote do:
          proc `patchProc` = body
          `patchProc`()
        for kind, refs in refs:
          for i in refs:
            let member {.inject.} = unpackMember(kind, memberNames[kind][i], getMPatchRef)
            procBody.add: quote do:
              `member`.patchProcs &= `patchProc`

    for elem in templ.elems:
      let sym = elem.sym
      case elem.kind
      of templText:
        addPatch(elem.text):
          `sym`.data = cstring(`code`)

      of templTag:
        for name, val in elem.attrs:
          let val = val.code
          procBody.add: quote do:
            `sym`.setAttrProperly(`name`, `val`)

        for event, action in elem.handlers:
          let action = action.code
          procBody.add: quote do:
            `sym`.addEventListener(`event`) do (_: Event):
              `action`
              `patchAll`()

        for name, val in elem.attrs:
          addPatch(val):
            `sym`.setAttrProperly(`name`, `code`)

      of templComponent:
        let component = elem.component.code
        procBody.add: quote do:
          `sym` = `component`.create()
        for name, val in elem.vars:
          let field = ident(name)
          let code = val.code
          let codeRaw = val.codeRaw
          procBody.add: quote do:
            when `name` in getFieldNames(`component`.L):
              `sym`.pubLetMembers.`field` = newPatchRef(`code`)
            elif `name` in getFieldNames(`component`.V):
              `sym`.pubVarMembers.`field` = `codeRaw`  #TODO: add err msg if not just a member
            else:
              assert false  #TODO: err msg
        procBody.add: quote do:
          `sym`.init()

      of templFor:
        let component = elem.forComponent
        let forVars = getForVars(elem.forHead.code)

        let patchForIters = genSym(nskProc, "patchForIters")

        # build proc that gets called by the generated instances:
        let patchContainer = genSym(nskProc, "patchContainer")
        var patchContainerDef = newStmtList()
        var patchContainerBody = newStmtList()
        for kind in [priv, pubVar]:
          for memberId in elem.forHead.refs[kind]:
            let memberNames = memberNames[kind][memberId]
            let member = unpackMember(kind, memberNames, getMPatchRef)
            patchContainerDef.add: quote do:
              `member`.patchProcs &= `patchForIters`
            patchContainerBody.add: quote do:
              for p in `member`.patchProcs:
                if p != `patchForIters`: p()
        patchContainerDef.add: quote do:
          proc `patchContainer` {.closure.} =
            `patchContainerBody`

        proc buildNewInstance: NimNode =
          result = newStmtList: quote do:
            `sym`.instances &= `component`.create()
          for forVar in forVars:
            let varIdent = ident($forVar)
            let td = forVar.getTypeInst()
            result.add:
              if td.kind == nnkVarTy:
                let td = td[0]
                quote do:
                  `sym`.instances[^1].pubVarMembers.`varIdent` =
                    PatchRef[`td`](
                      val: cast[ref `td`](addr `varIdent`),
                      patchProcs: @[`patchContainer`]
                    )
              else:
                quote do:
                  `sym`.instances[^1].pubLetMembers.`varIdent` = newPatchRef(`varIdent`)
          result.add: quote do:
            `sym`.instances[^1].init()

        # build proc that updates the instances (and adds/removes)
        var patchForItersBody = newStmtList()
        let iterId = genSym(nskVar, "i")
        var patchForItersForStmt = new elem.forHead.code[]
        let newInstance = buildNewInstance()
        let parent = elem.parent
        let getHook = elem.getHookProc
        var updateLetForVars = newStmtList()
        for forVar in forVars:
          if forVar.getTypeInst().kind != nnkVarTy:
            let forVar = ident($forVar)
            updateLetForVars.add: quote do:
              `sym`.instances[`iterId`].pubLetMembers.`forVar`.val[] = `forVar`
        patchForItersForStmt[^1] = quote do:
          if `iterId` < len(`sym`.instances):
            `updateLetForVars`
            patch `sym`.instances[`iterId`].pubLetMembers
            patch `sym`.instances[`iterId`].pubVarMembers
          else:
            debugEcho "mount new instance .."
            `newInstance`
            `sym`.instances[^1].mount(`parent`, `getHook`)
          inc `iterId`
        patchForItersBody.add: quote do:
          var `iterId` = 0
          `patchForItersForStmt`
          if `iterId` < len(`sym`.instances):
            debugEcho "detach instances .."
            for i in `iterId` ..< len(`sym`.instances):
              `sym`.instances[i].detach()
            `sym`.instances.setLen `iterId`

        var buildInstances = new elem.forHead.code[]
        buildInstances[^1] = buildNewInstance()

        procBody.add: quote do:
          proc `patchForIters` {.closure.}
          `patchContainerDef`
          `buildInstances`
          proc `patchForIters` {.closure.} = `patchForItersBody`

      of templIf: discard

    quote do:
      proc = `procBody`


  let mountProc = block:
    
    var withHookBody, withoutHookBody = newStmtList()

    proc addToBothBodys(node: NimNode) =
      withHookBody.add node
      withoutHookBody.add node

    for elem in templ.elems:
      let sym = elem.sym
      case elem.kind
      of templComponent:
        addToBothBodys:
          if elem.parentId < 0:
            quote do:
              `sym`.mount(`rootParent`, `getRootHook`)
          else:
            let parent = elem.parent
            quote do:
              `sym`.mount(`parent`, nil)

      of templFor:
        addToBothBodys:
          if elem.parentId < 0:
            quote do:
              for elem in `sym`.instances:
                elem.mount(`rootParent`, `getRootHook`)
          else:
            let parent = elem.parent
            quote do:
              for elem in `sym`.instances:
                elem.mount(`parent`, nil)

      of templIf: discard #TODO

      else:
        if elem.parentId < 0:
          withoutHookBody.add: quote do:
            `rootParent`.appendChild(`sym`)
          withHookBody.add: quote do:
            `rootParent`.insertBefore(`sym`, `getRootHook`())
        else:
          let parent = elem.parent
          addToBothBodys: quote do:
            `parent`.appendChild(`sym`)

    quote do:
      proc(parent: Node, getHook: proc: Node) =
        `rootParent` = parent
        `getRootHook` = getHook
        if `getRootHook` == nil: `withoutHookBody`
        else: `withHookBody`


  let detachProc = block:
    var procBody = newStmtList()
    for elem in templ.elems:
      if elem.parentId < 0:
        let sym = elem.sym
        procBody.add:
          case elem.kind
          of templText, templTag:
            quote do:
              `rootParent`.removeChild(`sym`)

          of templComponent:
            quote do:
                `sym`.detach()

          of templFor:
            quote do:
              for elem in `sym`.instances:
                elem.detach()

          of templIf: continue #TODO

    quote do:
      proc =
        `procBody`
        `rootParent` = nil

  let
    pubLetMembers = members[pubLet]
    pubVarMembers = members[pubVar]
    pubLetType = membersTypes[pubLet]
    pubVarType = membersTypes[pubVar]

  result = quote do:
    `pubMembersTypeDefs`
    Component[`pubLetType`, `pubVarType`](
      create: proc: ComponentInstance[`pubLetType`, `pubVarType`] =
        `privMembersTypeDef`
        `initMembers`
        `initCode`
        var `rootParent`: Node
        var `getRootHook`: proc: Node
        `patchAllDef`
        `defElems`
        ComponentInstance[`pubLetType`, `pubVarType`](
          init: `initProc`,
          mount: `mountProc`,
          detach: `detachProc`,
          pubLetMembers: `pubLetMembers`,
          pubVarMembers: `pubVarMembers`,
          getFirstNode: `getFirstNodeProc`
        )
    )

  #debugEcho repr result



macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  var
    memberNames: array[MemberKind, seq[string]]
    templBody = newEmptyNode()
    initCode = newStmtList()

  # --- collect init code, member names and template: ---

  proc scanBody(body: NimNode) =
    for stmt in body:
      if stmt.kind == nnkStmtList:
        scanBody stmt

      elif stmt.kind in {nnkCommand, nnkCall} and
         stmt[0].strVal =~= "templ":
            stmt.expectLen 2
            assert templBody.kind == nnkEmpty  #TODO: err msg
            templBody = stmt[1]

      else:
        if stmt.kind in {nnkLetSection, nnkVarSection}:
          let isVar = stmt.kind == nnkVarSection
          for stmtId, def in stmt:
            for symId, sym in def[0 ..< ^2]:
              if sym.kind == nnkPostfix:  # is pub?
                assert $sym[0] == "*"
                if isVar:
                  memberNames[pubVar] &= sym[1].strVal
                else:
                  memberNames[pubLet] &= sym[1].strVal
                stmt[stmtId][symId] = sym[1]
              elif isVar:
                memberNames[priv] &= sym.strVal

        initCode.add stmt

  scanBody body

  assert templBody.kind != nnkEmpty  #TODO: err msg
  var templ = parseTempl(templBody)

  # --- transfer code-blocks to initCode, for typing: ---

  proc collectCodeBlocks(templ: var Templ, fixNames: seq[string]): NimNode =
    result = newStmtList()
    
    for codeBlock in templ.codeBlocks:
      let code = codeBlock.code
      result.add:
        if codeBlock.isStmt:
          nnkBlockStmt.newTree(templCodeBlock, code)
        else:
          var fixMembers = newStmtList()
          for name in fixNames:
            fixMembers.add newLetStmt(ident(name), ident(name))
          quote do:
            {.hint[XDeclaredButNotUsed]:off.}
            discard(block:
              `fixMembers`
              block `templCodeBlock`:
                `code`
            )
            {.hint[XDeclaredButNotUsed]:on.}  

    for i, elem in templ.elems:
      case elem.kind
      of templFor:
        var forStmt = new templ.codeBlocks[elem.forHead].code[]
        forStmt[^1] = collectCodeBlocks(
          elem.forBody,
          deduplicate(fixNames & getForVars(forStmt).mapIt($it))
        )
        result.add forStmt

      of templIf:
        var ifStmt = nnkIfStmt.newTree()
        for (cond, body, _) in elem.elifBranches.mitems:
          let cond = templ.codeBlocks[cond].code
          ifStmt.add nnkElifBranch.newTree(
            cond,
            collectCodeBlocks(
              body,
              deduplicate(fixNames & getIfCondBindings(cond).mapIt($it))
            )
          )
        if Some((@body, _)) ?= elem.elseBody:
          ifStmt.add nnkElse.newTree(collectCodeBlocks(body, fixNames))
        result.add ifStmt

      else: discard

  var fixNames: seq[string]
  for names in memberNames: fixNames &= names
  initCode.add nnkBlockStmt.newTree(templCodeBlocks, collectCodeBlocks(templ, fixNames))

  # --- call typed macro: ---

  result = genAst(memberNames, templ = templ.toAstGen, initCode):
    componentTyped(memberNames, initTable[string, NimNode](), templ, initCode)

  #debugEcho repr result



proc run*(component: Component) =
  let inst = component.create()
  inst.init()
  inst.mount(document.body, nil)