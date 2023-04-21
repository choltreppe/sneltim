#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, sequtils, strutils, strformat, tables]
import ./utils


type
  TemplElemKind* = enum templText, templTag, templComponent, templFor
  TemplElem* = ref object
    elemSym: NimNode
    case kind: TemplElemKind
    of templText:
      text: NimNode
    of templTag:
      tag: string
      attrs, handlers: Table[string, NimNode]
      childs: seq[TemplElem]
    of templComponent:
      component: NimNode
      params: Table[string, NimNode]
    of templFor:
      forHead: seq[NimNode]
      forBody: seq[TemplElem]

  Templ* = seq[TemplElem]

func `$`*(templ: Templ, indent = 0): string =
  let indentStr = " ".repeat(indent)
  for elem in templ:
    result.add indentStr
    case elem.kind
    of templText:
      result.add elem.text.repr
    of templTag:
      result.add "<" & elem.tag
      for name, val in elem.attrs:
        result.add fmt" {name}=({val.repr})"
      for event, action in elem.handlers:
        result.add fmt" on[{event}]=({action.repr})"
      result.add ">"
      if len(elem.childs) >= 0:
        result.add "\n"
        result.add `$`(elem.childs, indent+1)
        result.add fmt"{indentStr}</{elem.tag}>"
    of templComponent:
      result.add "<%" & elem.component.repr
      for name, val in elem.params:
        result.add fmt" {name} = {val.repr}"
      result.add ">"
    of templFor:
      result.add "for " &
        elem.forHead[0 ..< ^1].mapIt(it.repr).join(", ") &
        " in " & elem.forHead[^1].repr & ":\n"
      result.add `$`(elem.forBody, indent+1)

    if elem.kind notin {templFor}:
      result.add "\n"


proc newTemplText*(s: string) = discard
proc newTemplTag*(name: string, params,handlers: tuple, content: proc = nil) = discard
proc newTemplComponent*(component: proc, params: tuple, content: proc = nil) = discard

let templDefLabel* {.compiletime.} = genSym(nskLabel, "templDef")


proc newTemplTextImpl(s: NimNode): NimNode =
  newCall(bindSym"newTemplText", s)

proc destructureCall(call: NimNode): tuple[callee, attrs, handlers: NimNode] =
  call.expectKind {nnkCall, nnkIdent, nnkSym}
  result.attrs = nnkTupleConstr.newTree()
  result.handlers = nnkTupleConstr.newTree()
  if call.kind == nnkCall:
    result.callee = call[0]
    if result.callee.kind == nnkAccQuoted:
      result.callee = result.callee[0]
    for param in call[1..^1]:
      param.expectKind nnkExprEqExpr
      if param[0].kind == nnkBracketExpr:
        param[0].expectLen 2
        param[0][0].expectKind {nnkIdent, nnkSym}
        let class = $param[0][0]
        case class
        of "on":
          param[0][1].expectKind {nnkIdent, nnkSym}
          result.handlers.add nnkExprColonExpr.newTree(
            param[0][1],
            nnkLambda.newTree(
              newEmptyNode(), newEmptyNode(), newEmptyNode(),
              nnkFormalParams.newTree(newEmptyNode()),
              newEmptyNode(), newEmptyNode(), 
              param[1]
            )
          )
        else:
          error fmt"invalid `{class}`"
      else:
        param[0].expectKind {nnkIdent, nnkSym}
        result.attrs.add nnkExprColonExpr.newTree(param[0], param[1])

  else:
    result.callee = call

proc cosiderCommandSyntax(call, body: NimNode): tuple[call, body: NimNode] =
  if body.kind == nnkEmpty and call.kind == nnkCommand:
    call.expectLen 2
    (call[0], call[1])
  else: (call, body)

proc newTemplTagImpl(call: NimNode, body = newEmptyNode()): NimNode =
  let (call, body) = cosiderCommandSyntax(call, body)
  let (callee, attrs, handlers) = destructureCall(call)
  callee.expectKind {nnkIdent, nnkSym}
  result = newCall(bindSym"newTemplTag", newLit($callee), attrs, handlers)
  if body.kind != nnkEmpty:
    result.add body.denestStmtList

proc newTemplComponentImpl(call: NimNode, body = newEmptyNode()): NimNode =
  let (call, body) = cosiderCommandSyntax(call, body)
  let (callee, attrs, handlers) = destructureCall(call)
  if len(handlers) > 0:
    for handler in handlers: error "components dont have event handlers", handler[0]
  callee.expectKind {nnkIdent, nnkSym}
  newCall(bindSym"newTemplComponent", callee, attrs)

template templToTypable(blockLabel, templDef: untyped) =

  macro text(s: string) {.inject.} =
    newTemplTextImpl(s)

  macro `<>`(call: untyped) {.inject.} =
    newTemplTagImpl(call)

  macro `<>`(call, body: untyped) {.inject.} =
    newTemplTagImpl(call, body)

  macro `<%>`(call: untyped) {.inject.} =
    newTemplComponentImpl(call)

  macro `<%>`(call, body: untyped) {.inject.} =
    newTemplComponentImpl(call, body)

  block blockLabel:
    templDef

macro html*(templDef: untyped) =
  newCall(bindSym"templToTypable", templDefLabel, templDef)


proc tupleDefToTable(tupleDef: NimNode): Table[string, NimNode] =
  tupleDef.expectKind nnkTupleConstr
  for node in tupleDef:
    node.expectKind nnkExprColonExpr
    result[nimIdentNormalize($node[0])] = node[1]

proc parseTempl*(node: NimNode): Templ =
  for node in node.denestStmtList.undoHiddenNodes:
    var elem = TemplElem(elemSym: genSym(nskVar, "elem"))

    case node.kind
    of nnkCall:
      case $node[0]
      of "newTemplText":
        node.expectLen 2
        elem.kind = templText
        elem.text = node[1]

      of "newTemplTag":
        node.expectLen 5
        elem.kind = templTag
        node[1].expectKind nnkStrLit
        elem.tag = node[1].strVal
        elem.attrs = tupleDefToTable(node[2])
        elem.handlers = tupleDefToTable(node[3])
        if node[4].kind == nnkEmpty: continue
        node[4].expectKind nnkLambda
        elem.childs = parseTempl(node[4][6])

      of "newTemplComponent":
        node.expectLen 4
        elem.kind = templComponent
        elem.component = node[1]
        elem.params = tupleDefToTable(node[2])

    of nnkForStmt:
      elem.kind = templFor
      for node in node[0 ..< ^1]:
        elem.forHead.add node
      elem.forBody.add parseTempl(node[^1])

    else: assert false

    result.add elem