import std/[macros, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
export sets, tables, dom, sequtils

import sneltim/templhtml


type
  Component*[P: proc] = object
    mount*: proc(parent, hook: Node)
    patch*: P
    detatch*: proc(parent: Node)

func newComponent[P: proc](mount: proc(parent, hook: Node), patch: P, detatch: proc(parent: Node)): Component[P] =
  Component[P](mount: mount, patch: patch, detatch: detatch)


let
  patchMap {.compiletime.} = genSym(nskConst, "patchMap")
  exportedVarMap {.compiletime.} = genSym(nskConst, "exportMap")
  exportedVarLabel {.compiletime.} = genSym(nsklabel, "exportVar")
  withPatchingTemplate {.compiletime.} = genSym(nskTemplate, "withPatching")
  patchSelf {.compiletime.} = genSym(nskVar, "patchSelf")


# just a container for recognition in typed macro
proc dynamicContent[T](v: T) = discard

{.pragma: exportField.}

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
    const `exportedVarMap` = `exportedVarMapImpl`


  var patchMapImpl = nnkBracket.newTree()  # patchId  ->  memberIds
  for patchId, memberIds in contentRefs:
    patchMapImpl.add: quote do: @`memberIds`

  result.add quote do:
    const `patchMap` = @`patchMapImpl`


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



macro component*(body: untyped): untyped =
  body.expectKind nnkStmtList

  let
    nodesArray = genSym(nskVar, "nodes")
    mountParent = genSym(nskParam, "parent")
    mountHook = genSym(nskParam, "hook")
    patchSelfChanged = genSym(nskParam, "changed")
    patchChanged = genSym(nskParam, "changed")
    detatchParent = genSym(nskParam, "parent")

  var
    createImpl = newStmtList()
    mountImpl = newStmtList()
    patchSelfImpl = newStmtList()
    patchImpl = newStmtList()
    detatchImpl = newStmtList()


  var templStr = ""
  var bodyForPatchGen = newStmtList()
  var patchParams = nnkFormalParams.newTree(newEmptyNode())

  for stmt in body:
    if stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
       stmt[0].strVal =~= "templ":
          stmt.expectLen 2
          assert templStr == ""
          templStr = stmt[1].strVal

    elif stmt.kind == nnkVarSection:
      # mark exported vars with labeled block:
      var varDefs = nnkVarSection.newTree()
      for def in stmt:
        if def[0].kind == nnkPostfix and $def[0][0] == "*":
          # patch proc:
          let memberVar = def[0][1]
          let paramVar = genSym(nskParam, $memberVar)
          patchParams.add nnkIdentDefs.newTree(paramVar, def[1], def[2])
          patchImpl.add newAssignment(memberVar, paramVar)
          # add var def:
          let td = def[1]
          let body = def[2]
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


  patchParams.add nnkIdentDefs.newTree(
    patchChanged,
    nnkBracketExpr.newTree(bindSym"array", newLit(len(patchParams) - 1), bindSym"bool"),
    newEmptyNode()
  )
  patchImpl.add: quote do:
    when len(`exportedVarMap`) > 0:
      var changed = newSeq[bool](len(`patchMap`))
      for i, v in `patchChanged`:
        changed[`exportedVarMap`[i]] = v
      `patchSelf`(changed)

  let patchDef = nnkLambda.newTree(
    newEmptyNode(), newEmptyNode(), newEmptyNode(),
    patchParams,
    newEmptyNode(), newEmptyNode(),
    patchImpl
  )


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
        debugEcho "patched: ", `nextPatchId`
    inc nextPatchId

  # build all procs and init
  proc generate(templ: TemplElem, parentId = -1) =
    inc nodeId
    let node = quote do: `nodesArray`[`nodeId`]

    case templ.kind
    of templTag:
      let name = templ.name
      createImpl.add: quote do:
        `node` = document.createElement(`name`)

      for attr, val in templ.attrs:
        case val.kind
        of valStr:
          let text = val.str
          createImpl.add: quote do:
            `node`.setAttr(`attr`, `text`)

        of valCode:
          let code = val.code.prefix("$")
          let setAttrCall = quote do:
            `node`.setAttr(`attr`, `code`)
          createImpl.add setAttrCall
          addPatchSelfContent(code, setAttrCall)

      for event, code in templ.handlers:
        createImpl.add: quote do:
          `node`.addEventListener(`event`) do (_: Event):
            `withPatchingTemplate`(`code`)

      let parentId = nodeId
      for child in templ.childs: generate(child, parentId)

    of templText:
      createImpl.add: quote do:
        `node` = document.createTextNode("")
      
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
        `node`.data = `buildText`

      createImpl.add assignText
      if hasCodeParts:
        addPatchSelfContent(buildText, assignText)

    else: return  #TODO

    mountImpl.add:
      if parentId < 0:
        detatchImpl.add: quote do:
          `detatchParent`.removeChild(`node`)
        quote do:
          if `mountHook` == nil:
            `mountParent`.appendChild(`node`)
          else:
            `mountParent`.insertBefore(`node`, `mountHook`)
      else:
        quote do: `nodesArray`[`parentId`].appendChild(`node`)

  for templ in templ:
    generate(templ)

  let nodesCount = nodeId + 1


  # add proc body:
  result = quote do:
    proc: auto =
      var `nodesArray`: array[`nodesCount`, Node]
      var `patchSelf`: proc(changed: seq[bool]) = nil
      generatePatchHandling(`bodyForPatchGen`)
      `createImpl`
      `patchSelf` = proc(`patchSelfChanged`: seq[bool]) = `patchSelfImpl`
      newComponent(
        proc(`mountParent`, `mountHook`: Node) = `mountImpl`,
        `patchDef`,
        proc(`detatchParent`: Node) = `detatchImpl`
      )

  debugEcho repr result