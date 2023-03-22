import std/[macros, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
export sets, tables, dom, sequtils

import ./private/templhtml


type
  ComponentInstance*[T: tuple] = object
    mount*: proc(parent, hook: Node)
    patch*: proc(vals: T, changed: seq[bool])
    detatch*: proc(parent: Node)

  Component*[T: tuple, exportedVars: static seq[string]] = object
    create*: proc: ComponentInstance[T]

  MemberDef = object
    mutable: bool
    exported: bool
    sym, T, val: NimNode

  TemplElemInfo = tuple[templ: TemplElem, sym, parent: NimNode]


let
  dynamicContentLabel {.compiletime.} = genSym(nskLabel, "dynamicContent")
  patchTable {.compiletime.} = ident"sneltimPatchTable"
  withPatchingTemplate {.compiletime.} = ident"sneltimWithPatching"
  patchSelf {.compiletime.} = ident"sneltimPatchSelf"

func `=~=`(a,b: string): bool = cmpIgnoreStyle(a, b) == 0


macro collectPatchTable(body: typed): untyped =
  result = newStmtList()

  var
    memberVars: seq[NimNode]
    memberProcs: seq[NimNode]
    memberProcRefs: seq[seq[int]]   # procId  ->  referenced memberIds
    contentRefs: seq[seq[int]]   # contentId  ->  referenced memberIds

  proc findMemberRefs(node: NimNode): seq[int] =
    case node.kind
    of nnkSym:
      if (let id = memberVars.find(node); id >= 0):
        result &= id
      elif (let id = memberProcs.find(node); id >= 0):
        result &= memberProcRefs[id]

    of complement(AtomicNodes):
      for child in node:
        result &= findMemberRefs(child)
      result = deduplicate(result)

    else: discard

  let body =
    if body.kind in {nnkStmtList, nnkStmtListExpr}: body
    else: newStmtList(body)

  for stmt in body:
    case stmt.kind
    of nnkVarSection:
      result.add stmt
      for def in stmt:
        memberVars.add def[0]

    of nnkProcDef, nnkFuncDef:
      result.add stmt
      memberProcRefs &= (findMemberRefs(stmt[3]) & findMemberRefs(stmt[6])).deduplicate
      memberProcs &= stmt[0]

    of nnkBlockStmt, nnkBlockExpr:
      if stmt[0].kind == nnkSym and stmt[0] == dynamicContentLabel:
        stmt.expectLen 2
        contentRefs &= findMemberRefs(stmt[1])
      
      else: result.add stmt
    else: result.add stmt

  var patchTableImpl = nnkBracket.newTree()  # patchId  ->  memberIds
  for patchId, memberIds in contentRefs:
    patchTableImpl.add: quote do: @`memberIds`

  result.add quote do:
    const `patchTable`: seq[seq[int]] = @`patchTableImpl`

  let withPatchingParam = genSym(nskParam, "body")
  let withPatchingImpl = block:
    var safePrevVal = newStmtList()
    var compare = newStmtList()
    let changed = genSym(nskVar, "changed")
    for id, memberVar in memberVars:
      let prev = genSym(nskLet, "prev")
      safePrevVal.add: quote do:
        let `prev` = `memberVar`
      compare.add: quote do:
        if `memberVar` != `prev`:
          `changed`[`id`] = true
    let len = len(memberVars)
    quote do:
      `safePrevVal`
      `withPatchingParam`
      var `changed` = newSeq[bool](`len`)
      `compare`
      `patchSelf`(`changed`)

  result.add quote do:
    template `withPatchingTemplate`(`withPatchingParam`) =
      `withPatchingImpl`
  debugEcho repr result


macro getExportedVarId*[T: tuple, exportedVars: static seq[string]](_: Component[T, exportedVars], name: static string): int =
  let i = exportedVars.find(name)
  assert i >= 0  #TODO: err msg
  newLit(i)


func getExportedVarNames(defs: seq[MemberDef]): seq[string] =
  for def in defs:
    if def.exported:
      result &= $def.sym


func buildElemsInit(elems: seq[TemplElemInfo]): NimNode =
  result = newStmtList()
  for (templ, sym, _) in elems:
    case templ.kind
    of templTag:
      let name = templ.name
      result.add: quote do:
        let `sym` = document.createElement(`name`)

      for attr, val in templ.attrs:
        case val.kind
        of valStr:
          let text = val.str
          result.add: quote do:
            `sym`.setAttr(`attr`, `text`)

        of valCode:
          let code = val.code.prefix("$")
          result.add: quote do:
            `sym`.setAttr(`attr`, `code`)

      for event, code in templ.handlers:
        result.add: quote do:
          `sym`.addEventListener(`event`) do (_: Event):
            `withPatchingTemplate`(`code`)

    of templComponent:
      let component = templ.sym
      let vals = genSym(nskVar, "vals")
      let defined = genSym(nskVar, "defined")
      result.add: quote do:
        let `sym` = `component`.create()
        var `vals`: `component`.T
        var `defined` = newSeq[bool](len(`component`.exportedVars))
      for name, valCode in templ.vars:
        result.add: quote do:
          `vals`[`component`.getExportedVarId(`name`)] = `valCode`
          `defined`[`component`.getExportedVarId(`name`)] = true
      result.add: quote do:
        `sym`.patch(`vals`, `defined`)

    of templText:
      var parts: seq[NimNode] = collect:
        for val in templ.text:
          case val.kind
          of valStr: newLit(val.str)
          of valCode:
            val.code.prefix("$")

      let buildText = parts.foldl(infix(a, "&", b))

      result.add: quote do:
        let `sym` = document.createTextNode(`buildText`)


func buildMountProc(elems: seq[TemplElemInfo]): NimNode =
  var procBody = newStmtList()

  let
    rootParent = genSym(nskParam, "parent")
    rootHook = genSym(nskParam, "hook")

  for (templ, sym, parent) in elems:
    procBody.add:
      if templ.kind == templComponent:
        if parent == nil:
          quote do:
            `sym`.mount(`rootParent`, `rootHook`)
        else:
          quote do:
            `sym`.mount(`parent`, nil)
      else:
        if parent == nil:
          quote do:
            if `rootHook` == nil:
              `rootParent`.appendChild(`sym`)
            else:
              `rootParent`.insertBefore(`sym`, `rootHook`)
        else:
          quote do:
            `parent`.appendChild(`sym`)

  quote do:
    proc(`rootParent`, `rootHook`: Node) = `procBody`


func buildPatchSelfProc(elems: seq[TemplElemInfo]): tuple[procDef: NimNode, anylizeCodes: seq[NimNode]] =
  var procBody = newStmtList()
  var anylizeCodes: seq[NimNode]

  let changed = genSym(nskParam, "changed")

  proc addContent(anylizeCode, patchCode: NimNode) =
    anylizeCodes.add anylizeCode
    let patchId = high(anylizeCodes)
    let it = ident"it"
    procBody.add: quote do:
      if `patchTable`[`patchId`].anyIt(`changed`[`it`]):
        `patchCode`

  for (templ, sym, parent) in elems:
    case templ.kind
    of templTag:
      for attr, val in templ.attrs:
        if val.kind == valCode:
          let code = val.code
          addContent(code): quote do:
            `sym`.setAttr(`attr`, $`code`)

    of templComponent:
      let component = templ.sym
      let vals = genSym(nskVar, "vals")
      let changed = genSym(nskVar, "changed")
      let anyChanges = genSym(nskVar, "anyChanges")
      procBody.add: quote do:
        var `vals`: `component`.T
        var `changed` = newSeq[bool](len(`component`.exportedVars))
        var `anyChanges` = false
      for name, valCode in templ.vars:
        addContent(valCode): quote do:
          `vals`[`component`.getExportedVarId(`name`)] = `valCode`
          `changed`[`component`.getExportedVarId(`name`)] = true
          `anyChanges` = true
      procBody.add: quote do:
        if `anyChanges`:
          `sym`.patch(`vals`, `changed`)

    of templText:
      var hasCodeParts = false
      var parts: seq[NimNode] = collect:
        for val in templ.text:
          case val.kind
          of valStr: newLit(val.str)
          of valCode:
            hasCodeParts = true
            val.code.prefix("$")

      let buildText = parts.foldl(infix(a, "&", b))

      if hasCodeParts:
        addContent(buildText): quote do:
          `sym`.data = `buildText`

  result.procDef = quote do:
    proc(`changed`: seq[bool]) = `procBody`

  result.anylizeCodes = anylizeCodes


func buildPatchProc(defs: seq[MemberDef]): tuple[procDef, paramType: NimNode] =
  var procBody = newStmtList()
  var T = nnkTupleConstr.newTree()
  
  let
    vals = genSym(nskParam, "vals")
    changed = genSym(nskParam, "changed")
    changedMembers = genSym(nskVar, "changedMembers")

  procBody.add newEmptyNode()  # to insert `changedMembers` decl

  var exportedId = 0
  var memberId = 0
  for def in defs:
    if def.exported:
      T.add:
        if def.T.kind == nnkEmpty: newCall(ident"typeof", def.val)
        else: def.T
      let sym = def.sym
      procBody.add: quote do:
        if `changed`[`exportedId`]:
          `sym` = `vals`[`exportedId`]
          `changedMembers`[`memberId`] = true
      inc exportedId

    if def.mutable or def.exported:
      inc memberId
  
  procBody[0] = quote do:
    var `changedMembers` = newSeq[bool](`memberId`)

  procBody.add: quote do:
    `patchSelf`(`changedMembers`)

  result.procDef = quote do:
    proc(`vals`: `T`, `changed`: seq[bool]) = `procBody`

  result.paramType = T


func buildDetatchProc(elems: seq[TemplElemInfo]): NimNode =
  var procBody = newStmtList()
  let rootParent = genSym(nskParam, "parent")
  for (templ, sym, parent) in elems:
    if parent == nil:
      procBody.add:
        if templ.kind == templComponent:
          quote do:
            `sym`.detatch(`rootParent`)
        else:
          quote do:
            `rootParent`.removeChild(`sym`)
  quote do:
    proc(`rootParent`: Node) = `procBody`


proc buildInitAndPatchTable(defs: seq[MemberDef], code: NimNode, anylizeCodes: seq[NimNode]): NimNode =
  var body = newStmtList()

  for def in defs:
    let identDef = nnkIdentDefs.newTree(def.sym, def.T, def.val)
    body.add:
      if def.mutable: nnkVarSection.newTree(identDef)
      else:           nnkLetSection.newTree(identDef)

  body.add code

  for code in anylizeCodes:
    body.add: quote do:
      block `dynamicContentLabel`:
        discard `code`

  quote do:
    collectPatchTable(`body`)


macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  var memberDefs: seq[MemberDef]
  var templStr = ""
  var code = newStmtList()  # code thats neither member defs nor template def

  for stmt in body:
    block checkStmt:
      if stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
         stmt[0].strVal =~= "templ":
            stmt.expectLen 2
            assert templStr == ""
            templStr = stmt[1].strVal
      else:
        for (kind, mutable) in [(nnkLetSection, false), (nnkVarSection, true)]:
          if stmt.kind == kind:
            for def in stmt:
              memberDefs.add:
                if def[0].kind == nnkPostfix and $def[0][0] == "*":
                  MemberDef(
                    mutable: mutable, exported: true,
                    sym: def[0][1], T: def[1], val: def[2]
                  )
                else:
                  MemberDef(
                    mutable: mutable, exported: false,
                    sym: def[0], T: def[1], val: def[2]
                  )
            break checkStmt
        code.add stmt

  assert templStr != ""
  let templ = parseTempl(templStr)

  var templElemsInfo: seq[TemplElemInfo]
  proc collectTemplElemInfo(elem: TemplElem, parent: NimNode = nil) =
    let sym = genSym(nskLet, "elem")
    templElemsInfo &= (elem, sym, parent)
    if elem.kind == templTag:
      for child in elem.childs:
        collectTemplElemInfo(child, sym)
  for elem in templ:
    collectTemplElemInfo(elem)

  let
    exportedVars = getExportedVarNames(memberDefs)
    initElems = buildElemsInit(templElemsInfo)
    mountProc = buildMountProc(templElemsInfo)
    (patchSelfProc, anylizeCodes) = buildPatchSelfProc(templElemsInfo)
    (patchProc, T) = buildPatchProc(memberDefs)
    detatchProc = buildDetatchProc(templElemsInfo)
    init = buildInitAndPatchTable(memberDefs, code, anylizeCodes)

  result = quote do:
    Component[`T`, @`exportedVars`](
      create: proc: ComponentInstance[`T`] =
        var `patchSelf`: proc(changed: seq[bool]) = nil
        `init`
        `initElems`
        `patchSelf` = `patchSelfProc`
        ComponentInstance[`T`](
          mount: `mountProc`,
          patch: `patchProc`,
          detatch: `detatchProc`
        )
    )

  debugEcho repr result