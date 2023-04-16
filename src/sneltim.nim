#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, genasts, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
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
    for p in pr.patchProcs: p()
    pr.prevVal = pr.val[]


type
  # for some reason I cant use Members as typeclass for Component
  Members = concept m
    m is ref object
    for f in m[].fields:
      f is PatchRef

  ComponentInstance[L,V] = object
    init: proc()
    mount: proc(parent, hook: Node)
    detach: proc()
    pubLetMembers: L
    pubVarMembers: V

  Component*[L,V] = object
    create: proc: ComponentInstance[L,V]

template instanceType(c: Component): type =
  ComponentInstance[c.L, c.V]

proc patch(members: ref object, init = false) =
  for member in members[].fields:
    patch member, init
  

let
  templCodeBlocks {.compiletime.} = genSym(nskLabel, "templCodeBlocks")
  templCodeBlock  {.compiletime.} = genSym(nskLabel, "templCodeBlock")


func `=~=`(a,b: string): bool = cmpIgnoreStyle(a, b) == 0

proc setAttrProperly*(node: Node, attr,val: string) =
  case attr
  of "value": node.value = val
  else: node.setAttr(attr, val)

func getForVars(forStmt: NimNode): seq[NimNode] =
  assert forStmt.kind == nnkForStmt
  for node in forStmt[0 ..< ^2]:
    if node.kind == nnkVarTuple:
      for sym in node: result.add sym
    else: result.add node



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
    getInheritedMember: seq[NimNode]
    memberProcs: seq[NimNode]
    memberProcRefs: seq[seq[int]]   # procId  ->  referenced memberIds

  type UnpackMemberLvl = enum justUnbind, getMPatchRef, getMVal

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
      pubLet: genSym(nskType, "pubLetType"),
      pubVar: genSym(nskType, "pubVarType"),
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
    let members = members[kind]
    let field = ident(name)
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
  var templForCodeBlocks: seq[NimNode]
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
        templForCodeBlocks &= unbind(node[^1], lvl=justUnbind, also=getForVars(node))

      of nnkLetSection:
        for defs in node:
          memberSyms &= defs[0 ..< ^2]

      else: discard

  collectCodeBlocks codeBlocksSection.denestStmtList

  # generate symbols for template elements
  for elem in templ.elems.mitems:
    elem.sym = genSym(nskVar, "elem")
    if elem.kind == templFor:
      elem.forComponent = genSym(nskLet, "forComponent")


  # --- generate instance: ---

  proc code(id: CodeBlockId): NimNode =
    templ.codeBlocks[id.int].code

  proc codeRaw(id: CodeBlockId): NimNode =
    templ.codeBlocks[id.int].codeRaw

  proc refs(id: CodeBlockId): array[MemberKind, seq[int]] =
    templ.codeBlocks[id.int].refs

  let
    rootParent = genSym(nskVar, "rootParent")
    rootHook = genSym(nskVar, "rootHook")


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
    var result = newStmtList()

    var nextForId = 0
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
        var forMemberNames: array[MemberKind, seq[string]]
        var componentBody = newStmtList()

        for forVar in getForVars(elem.forHead.code):
          assert forVar.kind == nnkSym
          let td = forVar.getTypeInst()
          let name = $forVar
          if td.kind == nnkVarTy:
            forMemberNames[pubVar].add name
            componentBody.add newVarStmt(
              ident(name),
              newCall(bindSym"default", unbind(td[0]))
            )
          else:
            forMemberNames[pubLet].add name
            componentBody.add newLetStmt(
              ident(name),
              newCall(bindSym"default", unbind(td))
            )

        # inherit members
        var membersInheritDef = nnkTableConstr.newTree()
        for kind, memberNames in memberNames:
          for name in memberNames:
            if forMemberNames.allIt(name notin it):
              forMemberNames[kind] &= name
              membersInheritDef.add nnkExprColonExpr.newTree(newLit(name), newCall(bindSym"newEmptyNode"))
              let val = unpackMember(kind, name, getMVal)
              componentBody.add:
                if kind == pubLet: newLetStmt(ident(name), val)
                else:              newVarStmt(ident(name), val)

        let codeBlocks = templForCodeBlocks[nextForId]
        inc nextForId
        componentBody.add: quote do:
          block `templCodeBlocks`:
            `codeBlocks`

        let componentDef = genAst(forMemberNames, membersInheritDef, templ = elem.forBody.toAstGen, componentBody):
          componentTyped(forMemberNames, toTable[string, NimNode](membersInheritDef), templ, componentBody)

        let component = elem.forComponent
        result.add: quote do:
          let `component` = `componentDef`
          var `sym`: seq[instanceType(`component`)]

    result


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
          let members = members[kind]
          for i in refs:
            let member {.inject.} = unpackMember(kind, memberNames[kind][i], getMPatchRef)
            procBody.add: quote do:
              `member`.patchProcs &= `patchProc`

    for elem in templ.elems:
      let sym = elem.sym
      case elem.kind
      of templText:
        addPatch(elem.text):
          `sym`.data = `code`

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
              `sym`.pubVarMembers.`field` = `codeRaw`
              debugEcho "set pub var"
              debugEcho `codeRaw`[].val[]
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
            let skipPatchId = genSym(nskLet, "skipPatch")
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
            `sym` &= `component`.create()
          for forVar in forVars:
            let varIdent = ident($forVar)
            let td = forVar.getTypeInst()
            result.add:
              if td.kind == nnkVarTy:
                let td = td[0]
                quote do:
                  `sym`[^1].pubVarMembers.`varIdent` =
                    PatchRef[`td`](
                      val: cast[ref `td`](addr `varIdent`),
                      patchProcs: @[`patchContainer`]
                    )
              else:
                quote do:
                  `sym`[^1].pubLetMembers.`varIdent` = newPatchRef(`varIdent`)
          result.add: quote do:
            `sym`[^1].init()

        # build proc that updates the instances (and adds/removes)
        var patchForItersBody = newStmtList()
        let iterId = genSym(nskVar, "i")
        var patchForItersForStmt = new elem.forHead.code[]
        let newInstance = buildNewInstance()
        let parent =
          if elem.parentId < 0: rootParent
          else: templ.elems[elem.parentId].sym
        let hook =
          if elem.hookId < 0: rootHook
          else: templ.elems[elem.hookId].sym
        patchForItersForStmt[^1] = quote do:
          if `iterId` < len(`sym`):
            patch `sym`[`iterId`].pubLetMembers
            patch `sym`[`iterId`].pubVarMembers
          else:
            debugEcho "mount new instance .."
            `newInstance`
            `sym`[^1].mount(`parent`, `hook`)
          inc `iterId`
        patchForItersBody.add: quote do:
          var `iterId` = 0
          `patchForItersForStmt`
          debugEcho `iterId`
          if `iterId` < len(`sym`):
            debugEcho "detach instances .."
            for i in `iterId` ..< len(`sym`):
              `sym`[i].detach()
            `sym`.setLen `iterId`

        var buildInstances = new elem.forHead.code[]
        buildInstances[^1] = buildNewInstance()

        procBody.add: quote do:
          proc `patchForIters` {.closure.}
          `patchContainerDef`
          `buildInstances`
          proc `patchForIters` {.closure.} = `patchForItersBody`

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
              `sym`.mount(`rootParent`, `rootHook`)
          else:
            let parent = templ.elems[elem.parentId].sym
            quote do:
              `sym`.mount(`parent`, nil)

      of templFor:
        addToBothBodys:
          if elem.parentId < 0:
            quote do:
              for elem in `sym`:
                elem.mount(`rootParent`, `rootHook`)
          else:
            let parent = templ.elems[elem.parentId].sym
            quote do:
              for elem in `sym`:
                elem.mount(`parent`, nil)

      else:
        if elem.parentId < 0:
          withoutHookBody.add: quote do:
            `rootParent`.appendChild(`sym`)
          withHookBody.add: quote do:
            `rootParent`.insertBefore(`sym`, `rootHook`)
        else:
          let parent = templ.elems[elem.parentId].sym
          addToBothBodys: quote do:
            `parent`.appendChild(`sym`)

    quote do:
      proc(parent, hook: Node) =
        `rootParent` = parent
        `rootHook` = hook
        if `rootHook` == nil: `withoutHookBody`
        else: `withHookBody`


  let detachProc = block:
    var procBody = newStmtList()
    let parent = genSym(nskParam, "parent")
    for elem in templ.elems:
      if elem.kind == templFor: continue
      if elem.parentId < 0:
        let sym = elem.sym
        procBody.add:
          if elem.kind == templComponent:
            quote do:
              `sym`.detach()
          else:
            quote do:
              `rootParent`.removeChild(`sym`)
    quote do:
      proc =
        `procBody`
        debugEcho "detached"
        `rootParent` = nil

  let
    pubLetMembers = members[pubLet]
    pubVarMembers = members[pubVar]
    pubLetType = membersTypes[pubLet]
    pubVarType = membersTypes[pubVar]

  result = quote do:
    `pubMembersTypeDefs`
    static: debugEcho `pubLetType` is Members
    Component[`pubLetType`, `pubVarType`](
      create: proc: ComponentInstance[`pubLetType`, `pubVarType`] =
        `privMembersTypeDef`
        `initMembers`
        `initCode`
        var `rootParent`, `rootHook`: Node
        `patchAllDef`
        `defElems`
        ComponentInstance[`pubLetType`, `pubVarType`](
          init: `initProc`,
          mount: `mountProc`,
          detach: `detachProc`,
          pubLetMembers: `pubLetMembers`,
          pubVarMembers: `pubVarMembers`
        )
    )

  debugEcho repr result



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
              let T =
                if def[^2].kind == nnkEmpty:
                  newCall(ident"typeof", def[^1])
                else: def[^2]
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
      if elem.kind == templFor:
        var forStmt = new templ.codeBlocks[elem.forHead.int].code[]
        forStmt[^1] = collectCodeBlocks(
          elem.forBody,
          deduplicate(fixNames & getForVars(forStmt).mapIt($it))
        )
        result.add forStmt

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