import std/[macros, genasts, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
export sets, tables, dom, sequtils

import ./private/templhtml


type
  Updates*[T: tuple] = object
    vals: T
    changed: seq[bool]

  ComponentInstance*[L,V] = object
    mount*: proc(parent, hook: Node)
    update*: proc(pubLet: Updates[L], pubVar: Updates[V])
    detach*: proc(parent: Node)

  Component*[L,V; pubLets,pubVars: static seq[string]] = object
    create*: proc(updateParent: proc(pubVar: Updates[V])): ComponentInstance[L,V]

func newUpdates[T: tuple](vals: T, changed: seq[bool]): Updates[T] =
  Updates[T](vals: vals, changed: changed)


type
  MemberKind = enum priv, pubLet, pubVar
  Members = array[MemberKind, seq[string]]
  MemberTypes = array[MemberKind, NimNode]

  CodeBlockId = int
  CodeBlock = tuple
    code: NimNode
    refs: array[MemberKind, seq[int]]

  TemplElemFlat[T: CodeBlock|CodeBlockId] = object
    sym: NimNode
    case kind: TemplElemKind
    of templText:
      text: T
    of templTag:
      tag: string
      attrs: Table[string, T]
      handlers: Table[string, T]
    of templComponent:
      component: T
      pubMembers: array[pubLet..pubVar, seq[string]]
      vars: Table[string, T]
    of templFor:
      forHead: T
      forBody: string
      forComponent: NimNode
      forPubMembers: array[pubLet..pubVar, NimNode]
      forPubMemberTypes: array[pubLet..pubVar, NimNode]
    parentId: int
    hookId: int = -1

  TemplFlat[T: CodeBlock|CodeBlockId] = seq[TemplElemFlat[T]]
  

# just a marker for compilation
func templCodeBlock(code: auto) = discard


func `=~=`(a,b: string): bool = cmpIgnoreStyle(a, b) == 0

proc setAttrProperly(node: Node, attr,val: string) =
  case attr
  of "value": node.value = val
  else: node.setAttr(attr, val)


func unbind(node: NimNode): NimNode =
  case node.kind
  of nnkSym:
    result = ident($node)
  of nnkHiddenAddr, nnkHiddenDeref:
    result = unbind(node[0])
  of nnkHiddenStdConv:
    result = unbind(node[1])
  of AtomicNodes - {nnkSym}:
    result = node
  else:
    result = node.kind.newTree()
    for node in node:
      result.add unbind(node)

func getForVars(forStmt: NimNode): seq[NimNode] =
  assert forStmt.kind == nnkForStmt
  for node in forStmt[0 ..< ^2]:
    if node.kind == nnkVarTuple:
      for sym in node: result.add sym
    else: result.add node

proc reactToChanges(
  code: NimNode,
  members: Members,
  patch, updateParent: NimNode
): NimNode =

  let
    privAnyChanges = genSym(nskVar, "privAnyChanges")
    pubVarAnyChanges = genSym(nskVar, "pubVarAnyChanges")
    privChanged = genSym(nskVar, "privChanged")
    pubVarChanged = genSym(nskVar, "pubVarChanged")
  var
    pubVarVals = nnkTupleConstr.newTree()
    safeOldState = newStmtList()
    checkChanges = newStmtList(quote do:
      var
        `privChanged`: seq[bool]
        `pubVarChanged`: seq[bool]
        `privAnyChanges` = false
        `pubVarAnyChanges` = false
    )

  for (kind, changed, anyChanges) in [(priv, privChanged, privAnyChanges), (pubVar, pubVarChanged, pubVarAnyChanges)]:
    for i, name in members[kind]:
      let memberSym = ident(name)
      let backupSym = genSym(nskLet, "backup")
      safeOldState.add: quote do:
        let `backupSym` = `memberSym`
      checkChanges.add: quote do:
        `changed` &= `memberSym` != `backupSym`
        `anyChanges` = `anyChanges` or `changed`[^1]
  for name in members[pubVar]:
    pubVarVals.add ident(name)
  
  let
    pubVarLen = len(members[pubVar])
    pubLetLen = len(members[pubLet])
  quote do:
    `safeOldState`
    `code`
    `checkChanges`
    if `privAnyChanges` or `pubVarAnyChanges`:
      `patch`([`privChanged`, newSeq[bool](`pubLetLen`), newSeq[bool](`pubVarLen`)])
    if `pubVarAnyChanges`:
      `updateParent`(newUpdates(`pubVarVals`, `pubVarChanged`))

# to unify otherwise redundant code between initElems and patch
proc buildComponentUpdate(
  elem: TemplElemFlat[CodeBlock],
  changedCond: proc(refs: array[MemberKind, seq[int]]): NimNode
): NimNode =

  assert elem.kind == templComponent

  let
    sym = elem.sym
    component = elem.component

  let
    pubLetChanged = genSym(nskVar, "pubLet")
    pubVarChanged = genSym(nskVar, "pubVar")
  var
    pubLetVals = nnkTupleConstr.newTree()
    pubVarVals = nnkTupleConstr.newTree()

  result = newStmtList()

  result.add: quote do:
    var `pubLetChanged`: seq[bool]
    var `pubVarChanged`: seq[bool]

  for (kind, changed, vals, typeName) in [(pubLet, pubLetChanged, pubLetVals, "L"), (pubVar, pubVarChanged, pubVarVals, "V")]:
    for i, name in elem.pubMembers[kind]:
      if name in elem.vars:
        let val = elem.vars[name]
        vals.add val.code
        let varChanged = changedCond(val.refs)
        result.add: quote do:
          `changed` &= `varChanged`
      else:
        let T = ident(typeName)
        vals.add: quote do:
          default(`component`.`T`)
        result.add: quote do:
          `changed` &= false

  result.add: quote do:
    `sym`.update(
      newUpdates(`pubLetVals`, `pubLetChanged`),
      newUpdates(`pubVarVals`, `pubVarChanged`)
    )

func buildCreateForInstance(
  elem: TemplElemFlat[CodeBlock],
  members: Members,
  patch, updateParent: NimNode
): NimNode =

  let
    sym = elem.sym
    forComponent = elem.forComponent
    pubLetVals = elem.forPubMembers[pubLet]
    pubVarVals = elem.forPubMembers[pubVar]
    PubVarType = elem.forPubMemberTypes[pubVar]
    parentUpdates = genSym(nskParam, "parentUpdates")

  var updateParentBody = newStmtList()
  for i, sym in elem.forPubMembers[pubVar]:
    updateParentBody.add: quote do:
      if `parentUpdates`.changed[`i`]:
        `sym`[] = `parentUpdates`.vals[`i`]
  updateParentBody = reactToChanges(updateParentBody, members, patch, updateParent)

  var asRefs = newStmtList()
  for sym in pubVarVals:
    asRefs.add: quote do:
      let `sym` = addr `sym`

  var captureCall = newCall(bindSym"capture")
  for sym in pubVarVals:
    captureCall.add sym

  captureCall.add: quote do:
    `forComponent`.create do (`parentUpdates`: Updates[`PubVarType`]):
      `updateParentBody`
      
  quote do:
    `sym`.add (
      `pubLetVals`, `pubVarVals`,
      block:
        `asRefs`
        `captureCall`
    )
    `sym`[^1].instance.update(
      newUpdates(`pubLetVals`, newSeqWith[bool](len(`forComponent`.pubLets), true)),
      newUpdates(`pubVarVals`, newSeqWith[bool](len(`forComponent`.pubVars), true))
    )


proc buildElemsInit(
  templ: TemplFlat[CodeBlock],
  members: Members,
  patch, updateParent: NimNode
): NimNode =

  result = newStmtList()
  for elem in templ:
    let sym = elem.sym
    case elem.kind
    of templTag:
      let tag = elem.tag
      result.add: quote do:
        var `sym` = document.createElement(`tag`)

      for name, val in elem.attrs:
        let val = val.code
        result.add: quote do:
          `sym`.setAttrProperly(`name`, `val`)

      for event, action in elem.handlers:
        let action = reactToChanges(action.code.unbind, members, patch, updateParent)
        debugEcho treerepr action
        result.add: quote do:
          `sym`.addEventListener(`event`) do (_: Event):
            `action`

    of templComponent:
      let component = elem.component.code

      let parentUpdates = genSym(nskParam, "updates")
      var updateParentBody = newStmtList()
      for i, name in elem.pubMembers[pubVar]:
        if name in elem.vars:
          let val = elem.vars[name].code
          updateParentBody.add: quote do:
            if `parentUpdates`.changed[`i`]:
              `val` = `parentUpdates`.vals[`i`]
      updateParentBody = reactToChanges(updateParentBody, members, patch, updateParent)

      result.add: quote do:
        var `sym` = `component`.create do(`parentUpdates`: Updates[`component`.V]):
          debugEcho "updateParent.."
          debugEcho `parentUpdates`
          `updateParentBody`

      result.add buildComponentUpdate(elem) do(_: array[MemberKind, seq[int]]) -> NimNode:
        ident"true"

    of templText:
      let text = elem.text.code
      result.add: quote do:
        var `sym` = document.createTextNode(`text`)

    of templFor:
      let
        forComponent = elem.forComponent
        templStr = elem.forBody
        templ = ident"templ"

      var membersDef = newStmtList()
      for (kind, sectionKind) in [(pubLet, nnkLetSection), (pubVar, nnkVarSection)]:
        var section = sectionKind.newTree()
        for i, sym in elem.forPubMembers[kind]:
          section.add nnkIdentDefs.newTree(
            sym.postfix("*"), newEmptyNode(),
            newCall(bindSym"default", elem.forPubMemberTypes[kind][i])
          )
        membersDef.add section
      
      var createInstances = elem.forHead.code
      createInstances[^2] = createInstances[^2].unbind
      createInstances[^1] = buildCreateForInstance(elem, members, patch, updateParent)

      let
        PubLetType = elem.forPubMemberTypes[pubLet]
        PubVarType = elem.forPubMemberTypes[pubVar]
      result.add: quote do:
        let `forComponent` = component:
          `membersDef`
          `templ` `templStr`
        var `sym`: seq[tuple[
          pubLets: `PubLetType`, pubVars: `PubVarType`,
          instance: ComponentInstance[`forComponent`.L, `forComponent`.V]
        ]]
        `createInstances`


proc buildPatchProc(
  templ: TemplFlat[CodeBlock],
  members: Members,
  patch, updateParent: NimNode
): NimNode =

  let changed = genSym(nskParam, "changed")

  var procBody = newStmtList()
  var initBody = newStmtList()

  # assert that members arent modified by patching:
  proc buildFixMembers: NimNode =
    result = newStmtList()
    for kind in [priv, pubVar]:
      for name in members[kind]:
        let sym = ident(name)
        result.add: quote do:
          let `sym` = `sym`

  func buildChangedCond(refs: array[MemberKind, seq[int]]): NimNode =
    var conds: seq[NimNode]
    for kind in MemberKind:
      for i in refs[kind]:
        conds.add: quote do:
          `changed`[`kind`][`i`]
    if len(conds) > 0:
      result = conds.foldl(infix(a, "or", b))

  for elem in templ:
    let sym = elem.sym
    var patchBlock = newStmtList()

    if elem.kind != templFor:
      patchBlock.add buildFixMembers()

    case elem.kind
    of templTag:
      for name, val in elem.attrs:
        if (let cond = buildChangedCond(val.refs); cond != nil):
          let val = val.code
          patchBlock.add: quote do:
            if `cond`: `sym`.setAttrProperly(`name`, `val`)

    of templComponent:
      patchBlock.add buildComponentUpdate(elem) do(refs: array[MemberKind, seq[int]]) -> NimNode:
        let cond = buildChangedCond(refs)
        if cond == nil: ident"false"
        else: cond

    of templText:
      if (let cond = buildChangedCond(elem.text.refs); cond != nil):
        let text = elem.text.code
        patchBlock.add: quote do:
          if `cond`: `sym`.data = `text`

    of templFor:
      if (let cond = buildChangedCond(elem.forHead.refs); cond != nil):
        let instanceId = genSym(nskVar, "i")

        var updateMemberCache = newStmtList()
        var changed = [pubLet: nnkBracket.newTree(), pubVar: nnkBracket.newTree()]
        for kind in pubLet..pubVar:
          let field = ident($kind & "s")
          for i, member in elem.forPubMembers[kind]:
            changed[kind].add: quote do:
              `member` != `sym`[`instanceId`].`field`[`i`]
          let members = elem.forPubMembers[kind]
          updateMemberCache.add: quote do:
            `sym`[`instanceId`].`field` = `members`

        var forStmt = elem.forHead.code

        var updateCall = quote do:
          `sym`[`instanceId`].instance.update()
        for kind in pubLet..pubVar:
          updateCall.add newCall(bindSym"newUpdates",
            elem.forPubMembers[kind],
            changed[kind].prefix("@")
          )
        let fixMembers = buildFixMembers()
        let createInstance = buildCreateForInstance(elem, members, patch, updateParent)
        let component = elem.forComponent
        let parent = templ[elem.parentId].sym
        let hook = if elem.hookId < 0: newNilLit()
                   else: templ[elem.hookId].sym
        forStmt[^1] = quote do:
          if `instanceId` < len(`sym`):
            `fixMembers`
            `updateCall`
            `updateMemberCache`
          else:
            `createInstance`
            `sym`[`instanceId`].instance.mount(`parent`, `hook`)
          inc `instanceId`
        patchBlock.add: quote do:
          if `cond`:
            var `instanceId` = 0
            `forStmt`
            if `instanceId` < len(`sym`):
              for elem in `sym`[`instanceId`..^1]:
                elem.instance.detach(`parent`)
              `sym`.setLen `instanceId`

    procBody.add: quote do:
      block: `patchBlock`

  quote do:
    proc(`changed`: array[MemberKind, seq[bool]]) =
      debugEcho "patch.."
      debugEcho `changed`
      `procBody`


proc buildMountProc(templ: TemplFlat[CodeBlock]): NimNode =
  var procBody = newStmtList()

  let
    rootParent = genSym(nskParam, "parent")
    rootHook = genSym(nskParam, "hook")

  for elem in templ:
    let sym = elem.sym
    procBody.add:
      case elem.kind
      of templComponent:
        if elem.parentId < 0:
          quote do:
            `sym`.mount(`rootParent`, `rootHook`)
        else:
          let parent = templ[elem.parentId].sym
          quote do:
            `sym`.mount(`parent`, nil)

      of templFor:
        if elem.parentId < 0:
          quote do:
            for elem in `sym`:
              elem.instance.mount(`rootParent`, `rootHook`)
        else:
          let parent = templ[elem.parentId].sym
          quote do:
            for elem in `sym`:
              debugEcho "mount for elem.."
              elem.instance.mount(`parent`, nil)

      else:
        if elem.parentId < 0:
          quote do:
            if `rootHook` == nil:
              `rootParent`.appendChild(`sym`)
            else:
              `rootParent`.insertBefore(`sym`, `rootHook`)
        else:
          let parent = templ[elem.parentId].sym
          quote do:
            `parent`.appendChild(`sym`)

  quote do:
    proc(`rootParent`, `rootHook`: Node) = `procBody`


proc buildUpdateProc(
  members: Members,
  memberTypes: MemberTypes,
  patch: NimNode
): NimNode =

  let params = [
    pubLet: genSym(nskParam, "pubLet"),
    pubVar: genSym(nskParam, "pubVar")
  ]

  var applyChanges = newStmtList()
  for kind, param in params:
    for i, name in members[kind]:
      let member = ident(name)
      applyChanges.add: quote do:
        if `param`.changed[`i`]:
          `member` = `param`.vals[`i`]

  let
    PubLetType = memberTypes[pubLet]
    PubVarType = memberTypes[pubVar]
    paramPubLet = params[pubLet]
    paramPubVar = params[pubVar]
    privLen = len(members[priv])

  quote do:
    proc(`paramPubLet`: Updates[`PubLetType`], `paramPubVar`: Updates[`PubVarType`]) =
      debugEcho "update.."
      `applyChanges`
      `patch`([newSeq[bool](`privLen`), `paramPubLet`.changed, `paramPubVar`.changed])


proc buildDetachProc(templ: TemplFlat): NimNode =
  var procBody = newStmtList()
  let parent = genSym(nskParam, "parent")
  for elem in templ:
    if elem.parentId < 0:
      let sym = elem.sym
      procBody.add:
        if elem.kind == templComponent:
          quote do:
            `sym`.detach(`parent`)
        else:
          quote do:
            `parent`.removeChild(`sym`)
  quote do:
    proc(`parent`: Node) = `procBody`


macro compileComponent(
  members: static Members,
  templFlat: static TemplFlat[CodeBlockId],
  body: typed
): untyped =

  let body =
    if body.kind in {nnkStmtList, nnkStmtListExpr}: body
    else: newStmtList(body)

  var
    memberSyms: seq[NimNode]
    memberTypes: MemberTypes
    memberProcs: seq[NimNode]
    memberProcRefs: seq[seq[int]]   # procId  ->  referenced memberIds
    codeBlocks: seq[CodeBlock]

  proc findMemberRefsAndUnbind(node: NimNode): tuple[refs: seq[int], node: NimNode] =
    case node.kind
    of nnkSym:
      if (let id = memberSyms.find(node); id >= 0):
        result.refs &= id
        result.node = ident($node)
      else:
        if (let id = memberProcs.find(node); id >= 0):
          result.refs &= memberProcRefs[id]
        result.node = node

    of nnkHiddenAddr, nnkHiddenDeref:
      result = findMemberRefsAndUnbind(node[0])

    of AtomicNodes - {nnkSym}:
      result.node = node

    else:
      result.node = node.kind.newTree()
      for child in node:
        let (refs, node) = findMemberRefsAndUnbind(child)
        result.refs.add refs
        result.node.add node
      result.refs = deduplicate(result.refs)

  var init = newStmtList()

  for stmt in body:
    case stmt.kind
    of nnkVarSection:
      for def in stmt:
        for i, sym in def[0 ..< ^2]:
          memberSyms.add sym
          def[i] = ident($sym)

      init.add stmt

    of nnkLetSection:
      for def in stmt:
        for i, sym in def[0 ..< ^2]:
          let singleDef = nnkIdentDefs.newTree(ident($sym), def[^2], def[^1])
          init.add:
            if $sym in members[pubLet]:
              memberSyms.add sym
              nnkVarSection.newTree(singleDef)
            else:
              nnkLetSection.newTree(singleDef)
          def[i] = ident($sym)

    of nnkProcDef, nnkFuncDef:
      let (refs, procDef) = findMemberRefsAndUnbind(stmt)
      debugEcho treerepr procDef
      memberProcRefs &= refs
      memberProcs &= stmt[0]
      init.add procDef

    of nnkCall:
      if $stmt[0] == "templCodeBlock":
        stmt.expectLen 2
        var codeBlock: CodeBlock
        let (refs, code) = findMemberRefsAndUnbind(stmt[1])
        codeBlock.code =
          if code.kind == nnkStmtList and len(code) == 1: code[0]
          else: code
        for memberId in refs:
          let name = $memberSyms[memberId]
          for kind in MemberKind:
            if (let i = members[kind].find(name); i >= 0):
              codeBlock.refs[kind] &= i
        codeBlocks &= codeBlock
      
    else: discard

  for kind, members in members:
    memberTypes[kind] = nnkTupleConstr.newTree()
  for sym in memberSyms:
    let name = $sym
    for kind in MemberKind:
      if (let i = members[kind].find(name); i >= 0):
        assert i == len(memberTypes[kind])
        memberTypes[kind].add getTypeInst(sym).unbind
        break
  for kind, td in memberTypes:
    if len(td) == 0:
      memberTypes[kind] = nnkTupleConstr.newTree()

  let templFlat = collect:
    for elem in templFlat:
      var res = TemplElemFlat[CodeBlock](
        sym: genSym(nskVar, "elem"),
        kind: elem.kind,
        parentId: elem.parentId,
        hookId: elem.hookId
      )
      case elem.kind
      of templText:
        res.text = codeBlocks[elem.text]

      of templTag:
        res.tag = elem.tag
        for name, val in elem.attrs:
          res.attrs[name] = codeBlocks[val]
        for event, action in elem.handlers:
          res.handlers[event] = codeBlocks[action]

      of templComponent:
        res.component = codeBlocks[elem.component]
        res.pubMembers = elem.pubMembers
        for name, val in elem.vars:
          res.vars[name] = codeBlocks[val]

      of templFor:
        res.forHead = codeBlocks[elem.forHead]
        res.forBody = elem.forBody
        res.forComponent = genSym(nskLet, "component")
        res.forPubMembers = [nnkTupleConstr.newTree(), nnkTupleConstr.newTree()]
        res.forPubMemberTypes = [nnkTupleConstr.newTree(), nnkTupleConstr.newTree()]
        for sym in getForVars(res.forHead.code):
          assert sym.kind == nnkSym
          let td = sym.getTypeInst()
          if td.kind == nnkVarTy:
            res.forPubMembers[pubVar].add ident($sym)
            res.forPubMemberTypes[pubVar].add td[0].unbind
          else:
            res.forPubMembers[pubLet].add ident($sym)
            res.forPubMemberTypes[pubLet].add td.unbind
      res


  let
    patch        = genSym(nskVar, "patch")
    updateParent = genSym(nskParam, "updateParent")

  let
    initElems = buildElemsInit(templFlat, members, patch, updateParent)
    patchProc = buildPatchProc(templFlat, members, patch, updateParent)
    mountProc = buildMountProc(templFlat)
    updateProc = buildUpdateProc(members, memberTypes, patch)
    detachProc = buildDetachProc(templFlat)

  let
    PubLetType = memberTypes[pubLet]
    PubVarType = memberTypes[pubVar]
    pubLetNames = members[pubLet]
    pubVarNames = members[pubVar]
  result = quote do:
    Component[`PubLetType`, `PubVarType`, @`pubLetNames`, @`pubVarNames`](
      create: proc(`updateParent`: proc(pubVar: Updates[`PubVarType`])): ComponentInstance[`PubLetType`, `PubVarType`] =
        var `patch`: proc(changed: array[MemberKind, seq[bool]])
        `init`
        `initElems`
        `patch` = `patchProc`
        ComponentInstance[`PubLetType`, `PubVarType`](
          mount: `mountProc`,
          update: `updateProc`,
          detach: `detachProc`
        )
    )

  #debugEcho repr result


macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  var
    members: Members
    templStr = ""
    initCode = newStmtList()

  proc scanBody(body: NimNode) =
    for stmt in body:
      if stmt.kind == nnkStmtList:
        scanBody stmt

      elif stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
         stmt[0].strVal =~= "templ":
            stmt.expectLen 2
            assert templStr == ""
            templStr = stmt[1].strVal

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
                  members[pubVar] &= sym[1].strVal
                else:
                  members[pubLet] &= sym[1].strVal
                stmt[stmtId][symId] = sym[1]
              elif isVar:
                members[priv] &= sym.strVal

        initCode.add stmt

  scanBody body

  assert templStr != ""
  let templ = parseTempl(templStr)

  var nextCodeBlockId = 0
  proc addCodeBlock(code: NimNode): int =
    initCode.add newCall(bindSym"templCodeBlock", code)
    result = nextCodeBlockId
    inc nextCodeBlockId

  func toStrGen(val: Val): NimNode =
    case val.kind
    of valStr: newLit(val.str)
    of valCode: val.code.prefix("$")

  var templFlatDef = nnkBracket.newTree()
  var nextElemId = 0
  proc flattenTempl(templ: TemplElem, parentId = -1): int =
    result = nextElemId
    inc nextElemId
    case templ.kind
    of templTag:
      var attrIds = nnkTableConstr.newTree()
      for name, val in templ.attrs:
        attrIds.add nnkExprColonExpr.newTree(newLit(name), newLit(addCodeBlock(val.toStrGen)))
      var handlerIds = nnkTableConstr.newTree()
      for name, action in templ.handlers:
        handlerIds.add nnkExprColonExpr.newTree(newLit(name), newLit(addCodeBlock(action)))
      let tag = templ.tag
      templFlatDef.add: quote do:
        TemplElemFlat[CodeBlockId](
          kind: templTag,
          tag: `tag`,
          attrs: toTable[string, CodeBlockId](`attrIds`),
          handlers: toTable[string, CodeBlockId](`handlerIds`),
          parentId: `parentId`
        )
      var predId = -1
      for child in templ.childs:
        let id = flattenTempl(child, result)
        if predId >= 0:
          templFlatDef[predId].add nnkExprColonExpr.newTree(ident"hookId", newLit(id))
        predId = id

    of templComponent:
      let component = templ.component
      let componentId = addCodeBlock(component)
      var varIds = nnkTableConstr.newTree()
      for name, val in templ.vars:
        varIds.add nnkExprColonExpr.newTree(newLit(name), newLit(addCodeBlock(val)))
      templFlatDef.add: quote do:
        TemplElemFlat[CodeBlockId](
          kind: templComponent,
          component: `componentId`,
          pubMembers: [
            pubLet: `component`.pubLets,
            pubVar: `component`.pubVars
          ],
          vars: toTable[string, CodeBlockId](`varIds`),
          parentId: `parentId`
        )

    of templText:
      let textId = addCodeBlock(templ.text.map(toStrGen).foldl(infix(a, "&", b)))
      templFlatDef.add: quote do:
        TemplElemFlat[CodeBlockId](kind: templText, text: `textId`, parentId: `parentId`)

    of templFor:
      let headId = addCodeBlock(templ.forHead)
      let forBody = templ.forBody
      templFlatDef.add: quote do:
        TemplElemFlat[CodeBlockId](kind: templFor, forHead: `headId`, forBody: `forBody`, parentId: `parentId`)
    
  for elem in templ:
    discard flattenTempl(elem)

  result = genAst(members, templFlatDef, initCode):
    compileComponent(members, @templFlatDef, initCode)


proc run*(component: Component) =
  component.create(nil).mount(document.body, nil)