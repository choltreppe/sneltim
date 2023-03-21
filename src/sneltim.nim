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


let
  memberVarsCount {.compiletime.} = ident"sneltimMembersCount"
  patchMap {.compiletime.} = ident"sneltimPatchMap"
  exportedVarMap {.compiletime.} = ident"sneltimExportMap"
  exportedVarLabel {.compiletime.} = genSym(nskLabel, "exportVar")
  withPatchingTemplate {.compiletime.} = ident"sneltimWithPatching"
  patchSelf {.compiletime.} = ident"sneltimPatchSelf"


# just a container for recognition in typed macro
proc dynamicContent[T](v: T) = discard

func `=~=`(a,b: string): bool = cmpIgnoreStyle(a, b) == 0


macro generatePatchHandling(body: typed): untyped =
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

  var exportedVarMapImpl = nnkBracket.newTree()

  for stmt in body:
    case stmt.kind
    of nnkVarSection:
      result.add stmt
      for def in stmt:
        memberVars.add def[0]
        if def[2].kind in {nnkBlockStmt, nnkBlockExpr} and def[2][0] == exportedVarLabel:
          exportedVarMapImpl.add newLit(high(memberVars))

    of nnkProcDef, nnkFuncDef:
      result.add stmt
      memberProcRefs &= (findMemberRefs(stmt[3]) & findMemberRefs(stmt[6])).deduplicate
      memberProcs &= stmt[0]

    of nnkCall, nnkCommand:
      if stmt[0].kind == nnkSym and $stmt[0] =~= "dynamicContent":
        stmt.expectLen 2
        contentRefs &= findMemberRefs(stmt[1])

    else:
      result.add stmt


  result.add: quote do:
    const `exportedVarMap`: seq[int] = @`exportedVarMapImpl`


  let l = len(memberVars)
  result.add: quote do:
    const `memberVarsCount` = `l`


  var patchMapImpl = nnkBracket.newTree()  # patchId  ->  memberIds
  for patchId, memberIds in contentRefs:
    patchMapImpl.add: quote do: @`memberIds`

  result.add quote do:
    const `patchMap`: seq[seq[int]] = @`patchMapImpl`


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



macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  let
    nodesArray = genSym(nskVar, "nodes")
    mountParent = genSym(nskParam, "parent")
    mountHook = genSym(nskParam, "hook")
    patchSelfChanged = genSym(nskParam, "changed")
    patchVals = genSym(nskParam, "vals")
    patchChanged = genSym(nskParam, "changed")
    detatchParent = genSym(nskParam, "parent")

  var
    initElems = newStmtList()
    mountImpl = newStmtList()
    patchSelfImpl = newStmtList()
    patchImpl = newStmtList()
    detatchImpl = newStmtList()
    T = nnkTupleConstr.newTree()


  var templStr = ""
  var bodyForPatchGen = newStmtList()
  var exportedVars: seq[string]
  let patchChangedMembers = genSym(nskVar, "changedMembers")

  patchImpl.add: quote do:
    var `patchChangedMembers` = newSeq[bool](`memberVarsCount`)

  for stmt in body:
    if stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
       stmt[0].strVal =~= "templ":
          stmt.expectLen 2
          assert templStr == ""
          templStr = stmt[1].strVal

    elif stmt.kind == nnkVarSection:
      var varDefs = nnkVarSection.newTree()
      for def in stmt:
        if def[0].kind == nnkPostfix and $def[0][0] == "*":
          let memberVar = def[0][1]
          let td = def[1]
          let body = def[2]
          exportedVars &= $memberVar
          let i = high(exportedVars)
          T.add:
            if td.kind == nnkEmpty: newCall(ident"typeof", body)
            else: td
          patchImpl.add: quote do:
            if `patchChanged`[`i`]:
              `memberVar` = `patchVals`[`i`]
              `patchChangedMembers`[`exportedVarMap`[`i`]] = true
          varDefs.add nnkIdentDefs.newTree(
            memberVar,
            td,
            nnkBlockStmt.newTree(exportedVarLabel,
              if body.kind == nnkEmpty:
                quote do: default(`td`)
              else: body
            )
          )
        else:
          varDefs.add def
      bodyForPatchGen.add varDefs

    else:
      bodyForPatchGen.add stmt

  assert templStr != ""
  let templ = parseTempl(templStr)


  patchImpl.add: quote do:
    `patchSelf`(`patchChangedMembers`)

  let patchDef = quote do:
    proc(`patchVals`: `T`, `patchChanged`: seq[bool]) =
      `patchImpl`


  var
    nodeId = -1
    nextPatchId = 0  

  proc addPatchSelfContent(anylizeCode, patchCode: NimNode) =
    bodyForPatchGen.add quote do:
      dynamicContent(`anylizeCode`)
    let it = ident"it"
    patchSelfImpl.add: quote do:
      if `patchMap`[`nextPatchId`].anyIt(`patchSelfChanged`[`it`]):
        `patchCode`
    inc nextPatchId

  # build all procs and init
  proc generate(templ: TemplElem, parentNode = newEmptyNode()) =
    let elem = genSym(nskLet, "elem")

    case templ.kind
    of templTag:
      let name = templ.name
      initElems.add: quote do:
        let `elem` = document.createElement(`name`)

      for attr, val in templ.attrs:
        case val.kind
        of valStr:
          let text = val.str
          initElems.add: quote do:
            `elem`.setAttr(`attr`, `text`)

        of valCode:
          let code = val.code.prefix("$")
          let setAttrCall = quote do:
            `elem`.setAttr(`attr`, `code`)
          initElems.add setAttrCall
          addPatchSelfContent(code): quote do:
            `setAttrCall`
            debugEcho "patched: ", `nextPatchId`

      for event, code in templ.handlers:
        initElems.add: quote do:
          `elem`.addEventListener(`event`) do (_: Event):
            `withPatchingTemplate`(`code`)

      for child in templ.childs: generate(child, elem)

    of templComponent:
      let component = templ.ident
      # init:
      block:
        let vals = genSym(nskVar, "vals")
        let changed = genSym(nskVar, "changed")
        initElems.add: quote do:
          let `elem` = `component`.create()
          var `vals`: `component`.T
          var `changed` = newSeq[bool](len(`component`.exportedVars))
        for name, valCode in templ.vars:
          initElems.add: quote do:
            `vals`[`component`.getExportedVarId(`name`)] = `valCode`
            `changed`[`component`.getExportedVarId(`name`)] = true
        initElems.add: quote do:
          `elem`.patch(`vals`, `changed`)
      # patch:
      block:
        let vals = genSym(nskVar, "vals")
        let changed = genSym(nskVar, "changed")
        let anyChanges = genSym(nskVar, "anyChanges")
        patchSelfImpl.add: quote do:
          var `vals`: `component`.T
          var `changed` = newSeq[bool](len(`component`.exportedVars))
          var `anyChanges` = false
        for name, valCode in templ.vars:
          addPatchSelfContent(valCode): quote do:
            `vals`[`component`.getExportedVarId(`name`)] = `valCode`
            `changed`[`component`.getExportedVarId(`name`)] = true
            `anyChanges` = true
        let componentName = $component  # just for debug output
        patchSelfImpl.add: quote do:
          if `anyChanges`:
            debugEcho "enter patching of ", `componentName`, ":"
            `elem`.patch(`vals`, `changed`)
      # mount, detatch:
      mountImpl.add:
        if parentNode.kind == nnkEmpty:
          detatchImpl.add: quote do:
            `elem`.detatch(`detatchParent`)
          quote do:
            `elem`.mount(`mountParent`, `mountHook`)
        else:
          quote do:
            `elem`.mount(`parentNode`, nil)
      return  # to skip default mount/detatch

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
      let assignText = quote do:
        `elem`.data = `buildText`

      initElems.add: quote do:
        let `elem` = document.createTextNode(`buildText`)

      if hasCodeParts:
        addPatchSelfContent(buildText): quote do:
          `assignText`
          debugEcho "patched: ", `nextPatchId`

    mountImpl.add:
      if parentNode.kind == nnkEmpty:
        # just need to detatch root elems
        detatchImpl.add: quote do:
          `detatchParent`.removeChild(`elem`)
        quote do:
          if `mountHook` == nil:
            `mountParent`.appendChild(`elem`)
          else:
            `mountParent`.insertBefore(`elem`, `mountHook`)
      else:
        quote do:
          `parentNode`.appendChild(`elem`)

  for templ in templ:
    generate(templ)

  let nodesCount = nodeId + 1


  # add proc body:
  result = quote do:
    Component[`T`, @`exportedVars`](
      create: proc: ComponentInstance[`T`] =
        var `patchSelf`: proc(changed: seq[bool]) = nil
        generatePatchHandling(`bodyForPatchGen`)
        `initElems`
        `patchSelf` = proc(`patchSelfChanged`: seq[bool]) = `patchSelfImpl`
        ComponentInstance[`T`](
          mount: proc(`mountParent`, `mountHook`: Node) = `mountImpl`,
          patch: `patchDef`,
          detatch: proc(`detatchParent`: Node) = `detatchImpl`
        )
    )

  debugEcho repr result