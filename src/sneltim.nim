import std/[macros, typetraits, sugar, sequtils, strutils, setutils, sets, tables, dom]
export sets, tables, dom, sequtils

import sneltim/templhtml


type
  Component* = object
    mount*: proc(parent, hook: Node)
    patch*: proc(changed: seq[bool])
    detatch*: proc(parent: Node)


const
  patchMapName = "sneltimPatchMap"
  withPatchingTemplateName ="sneltimWithPatching"
  patchSelfName = "sneltimPatchSelf"


# just a container for recognition in typed macro
proc dynamicContent[T](v: T) = discard


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


  body.expectKind nnkStmtList
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

    of nnkCall, nnkCommand:
      if stmt[0].kind == nnkSym and cmpIgnoreStyle($stmt[0], "dynamicContent") == 0:
        stmt.expectLen 2
        contentRefs &= findMemberRefs(stmt[1])

    else: discard


  var patchMapImpl = nnkBracket.newTree()  # patchId  ->  memberIds
  for patchId, memberIds in contentRefs:
    patchMapImpl.add: quote do: @`memberIds`

  let patchMap = ident(patchMapName)
  result.add quote do:
    let `patchMap`  = `patchMapImpl`


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
    let patchSelf = ident(patchSelfName)
    quote do:
      `safePrevVal`
      `withPatchingParam`
      var `changed` = newSeq[bool](`len`)
      `compare`
      `patchSelf`(`changed`)

  let withPatching = ident(withPatchingTemplateName)
  result.add quote do:
    template `withPatching`(`withPatchingParam`) =
      `withPatchingImpl`



macro component*(componentName, body: untyped): untyped =
  componentName.expectKind {nnkIdent, nnkSym}
  body.expectKind nnkStmtList

  var templStr = ""
  var bodyForPatchGen = newStmtList()
  for stmt in body:
    if stmt.kind in {nnkCommand, nnkCall, nnkCallStrLit} and
       cmpIgnoreStyle(stmt[0].strVal, "templ") == 0:
          stmt.expectLen 2
          assert templStr == ""
          templStr = stmt[1].strVal
    else:
      bodyForPatchGen.add stmt

  assert templStr != ""
  let templ = parseTempl(templStr)

  let
    nodesArray    = genSym(nskVar, "nodes")
    mountParent   = genSym(nskParam, "parent")
    mountHook     = genSym(nskParam, "hook")
    patchChanged  = genSym(nskParam, "changed")
    detatchParent = genSym(nskParam, "parent")

  var
    createBody  = newStmtList()
    mountBody   = newStmtList()
    patchBody   = newStmtList()
    detatchBody = newStmtList()
  
  var
    nodeId = -1
    nextPatchId = 0

  let patchMap = ident(patchMapName)
  let withPatching = ident(withPatchingTemplateName)
  let patchSelf = ident(patchSelfName)

  proc addPatchContent(anylizeCode, patchCode: NimNode) =
    bodyForPatchGen.add quote do:
      dynamicContent(`anylizeCode`)
    let it = ident"it"
    patchBody.add: quote do:
      if `patchMap`[`nextPatchId`].anyIt(`patchChanged`[`it`]):
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
      createBody.add: quote do:
        `node` = document.createElement(`name`)

      for attr, val in templ.attrs:
        case val.kind
        of valStr:
          let text = val.text
          createBody.add: quote do:
            `node`.setAttr(`attr`, `text`)

        of valCode:
          let code = val.code.prefix("$")
          let setAttrCall = quote do:
            `node`.setAttr(`attr`, `code`)
          createBody.add setAttrCall
          addPatchContent(code, setAttrCall)

      for event, code in templ.handlers:
        createBody.add: quote do:
          `node`.addEventListener(`event`) do (_: Event):
            `withPatching`(`code`)

      let parentId = nodeId
      for child in templ.childs: generate(child, parentId)

    of templText:
      createBody.add: quote do:
        `node` = document.createTextNode("")
      
      var hasCodeParts = false
      var parts: seq[NimNode] = collect:
        for val in templ.text:
          case val.kind
          of valStr: newLit(val.text)
          of valCode:
            hasCodeParts = true
            val.code.prefix("$")

      let buildText = parts.foldl(infix(a, "&", b))
      let assignText = quote do:
        `node`.data = `buildText`

      createBody.add assignText
      if hasCodeParts:
        addPatchContent(buildText, assignText)

    else: discard  #TODO

    mountBody.add:
      if parentId < 0:
        detatchBody.add: quote do:
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

  quote do:
    let `componentName` = proc: Component =
      var `nodesArray`: array[`nodesCount`, Node]
      var `patchSelf`: proc(changed: seq[bool]) = nil
      generatePatchHandling(`bodyForPatchGen`)
      `createBody`
      `patchSelf` = proc(`patchChanged`: seq[bool]) = `patchBody`
      Component(
        mount: proc(`mountParent`, `mountHook`: Node) = `mountBody`,
        patch: `patchSelf`,
        detatch: proc(`detatchParent`: Node) = `detatchBody`
      )