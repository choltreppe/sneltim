import std/[macros, genasts, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
export sets, tables, dom, sequtils

import ./private/templhtml


func `=~=`(a,b: string): bool = cmpIgnoreStyle(a, b) == 0


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

  TemplElemFlat = ref object
    sym: NimNode
    case kind: TemplElemKind
    of templText:
      text: CodeBlockId
    of templTag:
      tag: string
      attrs: Table[string, CodeBlockId]
      handlers: Table[string, CodeBlockId]
    of templComponent:
      component: CodeBlockId
      pubMembers: array[pubLet..pubVar, seq[string]]
      vars: Table[string, CodeBlockId]
    parentId: int
  TemplFlat = seq[TemplElemFlat]

  CodeBlock = tuple
    code: NimNode
    refs: array[MemberKind, seq[int]]


func templCodeBlock(code: auto) = discard


proc buildComponentUpdate(
  elem: TemplElemFlat,
  codeBlocks: seq[CodeBlock],
  changedCond: proc(valId: int): NimNode
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
        let valId = elem.vars[name]
        vals.add codeBlocks[valId].code
        let varChanged = changedCond(valId)
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


proc buildElemsInit(
  templ: TemplFlat,
  codeBlocks: seq[CodeBlock],
  members: Members,
  patch, updateParent: NimNode
): NimNode =

  proc reactToChanges(code: NimNode): NimNode =
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

  result = newStmtList()
  for elem in templ:
    let sym = elem.sym
    case elem.kind
    of templTag:
      let tag = elem.tag
      result.add: quote do:
        let `sym` = document.createElement(`tag`)

      for name, valId in elem.attrs:
        let val = codeBlocks[valId].code
        result.add: quote do:
          `sym`.setAttr(`name`, `val`)

      for event, codeId in elem.handlers:
        let code = reactToChanges(codeBlocks[codeId].code)
        result.add: quote do:
          `sym`.addEventListener(`event`) do (_: Event):
            `code`

    of templComponent:
      let component = codeBlocks[elem.component].code

      let parentUpdates = genSym(nskParam, "updates")
      var updateParentBody = newStmtList()
      for i, name in elem.pubMembers[pubVar]:
        if name in elem.vars:
          let val = codeBlocks[elem.vars[name]].code
          updateParentBody.add: quote do:
            if `parentUpdates`.changed[`i`]:
              `val` = `parentUpdates`.vals[`i`]

      updateParentBody = reactToChanges(updateParentBody)
      result.add: quote do:
        let `sym` = `component`.create do(`parentUpdates`: Updates[`component`.V]):
          debugEcho "updateParent.."
          debugEcho `parentUpdates`
          `updateParentBody`

      result.add buildComponentUpdate(elem, codeBlocks) do(valId: int) -> NimNode:
        ident"true"

    of templText:
      let text = codeBlocks[elem.text].code
      result.add: quote do:
        let `sym` = document.createTextNode(`text`)


proc buildPatchProc(
  templ: TemplFlat,
  codeBlocks: seq[CodeBlock],
  members: Members
): NimNode =

  let changed = genSym(nskParam, "changed")

  var procBody = newStmtList()
  var initBody = newStmtList()

  # assert that members arent modified by patching:
  for members in members:
    for name in members:
      let sym = ident(name)
      procBody.add: quote do:
        let `sym` = `sym`


  func buildChangedCond(i: CodeBlockId): NimNode =
    var conds: seq[NimNode]
    for kind in MemberKind:
      for i in codeBlocks[i].refs[kind]:
        conds.add: quote do:
          `changed`[`kind`][`i`]
    if len(conds) > 0:
      result = conds.foldl(infix(a, "or", b))

  for elem in templ:
    let sym = elem.sym
    case elem.kind
    of templTag:
      for name, valId in elem.attrs:
        if (let cond = buildChangedCond(valId); cond != nil):
          let val = codeBlocks[valId].code
          procBody.add: quote do:
            if `cond`: `sym`.setAttr(`name`, `val`)

    of templComponent:
      procBody.add buildComponentUpdate(elem, codeBlocks) do(valId: int) -> NimNode:
        let cond = buildChangedCond(valId)
        if cond == nil: ident"false"
        else: cond


    of templText:
      if (let cond = buildChangedCond(elem.text); cond != nil):
        let text = codeBlocks[elem.text].code
        procBody.add: quote do:
          if `cond`: `sym`.data = `text`

  quote do:
    proc(`changed`: array[MemberKind, seq[bool]]) =
      debugEcho "patch.."
      debugEcho `changed`
      `procBody`


proc buildMountProc(templ: TemplFlat): NimNode =
  var procBody = newStmtList()

  let
    rootParent = genSym(nskParam, "parent")
    rootHook = genSym(nskParam, "hook")

  for elem in templ:
    let sym = elem.sym
    procBody.add:
      if elem.kind == templComponent:
        if elem.parentId < 0:
          quote do:
            `sym`.mount(`rootParent`, `rootHook`)
        else:
          let parent = templ[elem.parentId].sym
          quote do:
            `sym`.mount(`parent`, nil)
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
  templFlat: static TemplFlat,
  body: typed
): untyped =

  let body =
    if body.kind in {nnkStmtList, nnkStmtListExpr}: body
    else: newStmtList(body)

  var templFlat = templFlat
  for elem in templFlat.mitems:
    elem.sym = genSym(nskLet, "elem")

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

    of complement(AtomicNodes):
      result.node = node.kind.newTree()
      for child in node:
        let (refs, node) = findMemberRefsAndUnbind(child)
        result.refs.add refs
        result.node.add node
      result.refs = deduplicate(result.refs)

    else:
      result.node = node

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
        for sym in def[0 ..< ^2]:
          let singleDef = nnkIdentDefs.newTree(ident($sym), def[^2], def[^1])
          init.add:
            if $sym in members[pubLet]:
              memberSyms.add sym
              nnkVarSection.newTree(singleDef)
            else:
              nnkLetSection.newTree(singleDef)

    of nnkProcDef, nnkFuncDef:
      let (refs, procDef) = findMemberRefsAndUnbind(stmt)
      memberProcRefs &= refs
      memberProcs &= stmt[0]
      init.add procDef

    of nnkCall:
      if $stmt[0] == "templCodeBlock":
        stmt.expectLen 2
        var codeBlock: CodeBlock
        let (refs, code) = findMemberRefsAndUnbind(stmt[1])
        codeBlock.code = code
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
        memberTypes[kind].add getType(sym)
        break


  let
    patch        = genSym(nskVar, "patch")
    updateParent = genSym(nskParam, "updateParent")

  let
    initElems = buildElemsInit(templFlat, codeBlocks, members, patch, updateParent)
    patchProc = buildPatchProc(templFlat, codeBlocks, members)
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

  debugEcho repr result


macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  var
    members: Members
    templStr = ""
    initCode = newStmtList()

  for stmt in body:
    if stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
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
  var elemId = -1
  proc flattenTempl(templ: TemplElem, parentId = -1) =
    inc elemId
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
        TemplElemFlat(
          kind: templTag,
          tag: `tag`,
          attrs: toTable[string, CodeBlockId](`attrIds`),
          handlers: toTable[string, CodeBlockId](`handlerIds`),
          parentId: `parentId`
        )
      let ownId = elemId
      for child in templ.childs:
        flattenTempl(child, ownId)

    of templComponent:
      let component = templ.component
      let componentId = addCodeBlock(component)
      var varIds = nnkTableConstr.newTree()
      for name, val in templ.vars:
        varIds.add nnkExprColonExpr.newTree(newLit(name), newLit(addCodeBlock(val)))
      templFlatDef.add: quote do:
        TemplElemFlat(
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
        TemplElemFlat(kind: templText, text: `textId`, parentId: `parentId`)
    
  for elem in templ:
    flattenTempl(elem)

  result = genAst(members, templFlatDef, initCode):
    compileComponent(members, @templFlatDef, initCode)
