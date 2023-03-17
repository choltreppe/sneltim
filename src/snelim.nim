import std/[macros, typetraits, sugar, sequtils, strutils, sets, tables, dom]
export sets, dom

import snelim/templhtml


type
  Component* = object
    mount*: proc(parent, hook: Node)
    patch*: proc(changed: HashSet[string])
    detatch*: proc(parent: Node)


# -- MemberVar is for markind components memeber vars too find refs in procs --

type MemberVar[T] = distinct T

type MemberVarRefs = HashSet[string]

func initMemberVarRefs: MemberVarRefs = discard

var memberVarRefs {.compiletime.}: MemberVarRefs

macro checkMemberVarRef[T](v: MemberVar[T]): T =
  memberVarRefs.incl v.strVal
  quote do: `v`.distinctBase

template checkMemberVarRef[T: not MemberVar](v: T): T = v

# attatch `findMemberVar` to all refed idents
func findMemberVarRefs(body: NimNode, clear = true): NimNode =
  proc search(node: NimNode): NimNode =

    template searchAt(i: int) =
      result = node
      result[i] = search(node[i])

    case node.kind:
    of nnkIdent:
      result = newCall(bindSym"checkMemberVarRef", node)

    of nnkDotExpr: searchAt(0)

    of nnkIdentDefs: searchAt(2)

    of nnkStmtList, nnkVarTuple, nnkPar, nnkDerefExpr, nnkIfExpr, nnkElseExpr, nnkIfStmt, nnkElse, nnkLetSection, nnkVarSection, nnkAsgn:
      result = node.kind.newTree()
      for node in node:
        result.add search(node)

    of nnkDotCall .. nnkPrefix, nnkBracket, nnkExprEqExpr, nnkExprColonExpr, nnkObjConstr, nnkElifExpr, nnkElifBranch, nnkBlockStmt, nnkBlockExpr:
      result = node.kind.newTree(node[0])
      for node in node[1..^1]:
        result.add search(node)

    of nnkLambda:
      result = node
      for i, node in node[3][1..^1]:
        result[i][2] = search(node[2])  # default val
      result[7] = search(node[7])

    else:
      result = node #TODO

  let body = search(body)
  
  quote do:
    when `clear`:
      static: memberVarRefs = initMemberVarRefs()
    `body`



macro component*(componentName, body: untyped) =
  componentName.expectKind {nnkIdent, nnkSym}
  body.expectKind nnkStmtList

  var varNames: seq[string]
  var varDefs = nnkVarSection.newTree()
  var templStr = ""

  for stmt in body:
    case stmt.kind
    of nnkVarSection:
      for def in stmt:
        varNames.add def[0].strVal.nimIdentNormalize
        var def = def
        if def[2].kind != nnkEmpty: def[2] = newCall(bindSym"MemberVar", def[2])
        varDefs.add def

    of nnkCommand, nnkCall, nnkCallStrLit:
      if cmpIgnoreStyle(stmt[0].strVal, "html") == 0:
        stmt.expectLen 2
        assert templStr == ""
        templStr = stmt[1].strVal

    else: discard

  assert templStr != ""
  let templ = parseTempl(templStr)

  let
    nodesArray    = genSym(nskVar, "nodes")
    refsArray     = genSym(nskVar, "refs")
    mountParent   = genSym(nskParam, "parent")
    mountHook     = genSym(nskParam, "hook")
    patchChanged  = genSym(nskParam, "changed")
    detatchParent = genSym(nskParam, "parent")

  var
    nodeId      = -1
    createBody  = newStmtList()
    mountBody   = newStmtList()
    patchBody   = newStmtList()
    detatchBody = newStmtList()

  # build all procs and init
  proc generate(templ: TemplElem, parentId = -1) =
    inc nodeId
    let node = quote do: `nodesArray`[`nodeId`]
    let refs = quote do: `refsArray`[`nodeId`]

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
          let code = findMemberVarRefs( val.code).prefix("$")
          let setAttrCall = quote do:
            `node`.setAttr(`attr`, `code`)
          createBody.add quote do:
            `setAttrCall`
            static: `refs` = memberVarRefs
          patchBody.add: quote do:
            when len(`refs`) > 0:
              if len(`patchChanged` * static(`refs`)) > 0:
                `setAttrCall`

      let parentId = nodeId
      for child in templ.childs: generate(child, parentId)

    of templText:
      createBody.add: quote do:
        `node` = document.createTextNode("")
        static:
          memberVarRefs = initMemberVarRefs()

      var parts: seq[NimNode] = collect:
        for val in templ.text:
          case val.kind
          of valStr: newLit(val.text)
          of valCode: findMemberVarRefs(val.code, clear=false).prefix("$")

      let buildText = parts.foldl(infix(a, "&", b))
      createBody.add: quote do:
        `node`.data = `buildText`
        static: `refs` = memberVarRefs
      patchBody.add: quote do:
        when len(`refs`) > 0:
          if len(`patchChanged` * static(`refs`)) > 0:
            `node`.data = `buildText`

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

  result = quote do:
    var `refsArray` {.compiletime.}: array[`nodesCount`, MemberVarRefs]
    let `componentName` = proc: Component =
      `varDefs`
      var `nodesArray`: array[`nodesCount`, Node]
      `createBody`
      Component(
        mount: proc(`mountParent`, `mountHook`: Node) = `mountBody`,
        patch: proc(`patchChanged`: HashSet[string]) = `patchBody`,
        detatch: proc(`detatchParent`: Node) = `detatchBody`
      )

  #debugEcho result.repr