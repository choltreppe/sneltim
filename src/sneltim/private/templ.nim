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
  TemplElemKind* = enum templText, templTag, templComponent, templSlot, templFor
  TemplElem* = ref object
    sym*: NimNode
    case kind*: TemplElemKind
    of templText:
      text*: NimNode

    of templTag:
      tag*: string
      attrs*: Table[string, tuple[val: NimNode, bound: bool]]
      handlers*: Table[string, NimNode]
      childs*: seq[TemplElem]

    of templComponent:
      component*: NimNode
      params*: Table[string, NimNode]
      slots*: Table[string, Templ]

    of templSlot:
      slotName*: string

    of templFor:
      forHead*: NimNode
      forBody*: Templ
      forComponent*: NimNode

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
      for name, (val, bound) in elem.attrs:
        result.add:
          if bound: fmt" bind[{name}]=({val.repr})"
          else:     fmt" {name}=({val.repr})"
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
      let indentStr = " ".repeat(indent+1)
      for name, body in elem.slots:
        result.add &"{indentStr}<..{name}>\n"
        result.add `$`(body, indent+2)
        result.add fmt"{indentStr}</..{name}>"
    of templSlot:
      result.add fmt"<..{elem.slotName}>"
    of templFor:
      result.add "for " &
        elem.forHead[0 ..< ^2].mapIt(it.repr).join(", ") &
        " in " & elem.forHead[^2].repr & ":\n"
      result.add `$`(elem.forBody, indent+1)

    if elem.kind notin {templFor}:
      result.add "\n"


proc newTemplText*(s: string) = discard
proc newTemplTag*(name: string, params,handlers: tuple, content: proc = nil) = discard
proc newTemplComponent*(component: proc, params: tuple, content: proc = nil) = discard
proc newTemplSlot*(name: string, content: proc = nil) = discard

let templDefLabel* {.compiletime.} = genSym(nskLabel, "templDef")


proc newTemplTextImpl(s: NimNode): NimNode =
  newCall(bindSym"newTemplText", s)

proc destructureCall(call: NimNode, bindable=true): tuple[callee, attrs, handlers: NimNode] =
  let call = call.unquote
  call.expectKind {nnkCall, nnkIdent, nnkSym}
  result.attrs = nnkTupleConstr.newTree()
  result.handlers = nnkTupleConstr.newTree()

  case call.kind
  of nnkCall:
    result.callee = call[0].unquote
    for param in call[1..^1]:
      param.expectKind nnkExprEqExpr
      let val = param[1]

      case param[0].kind
      of nnkBracketExpr:
        param[0].expectLen 2
        let class = param[0][0]
        class.expectKind {nnkIdent, nnkSym}
        if $class == "on":
          param[0][1].expectKind {nnkIdent, nnkSym}
          result.handlers.add nnkExprColonExpr.newTree(
            param[0][1],
            quote do:
              proc = `val`
          )
        else:
          error fmt"invalid `{class}`", class

      of nnkBind:
        if not bindable:
          error fmt"cant bind values on component", param[0]
        param[0][0].expectKind nnkBracket
        param[0][0].expectLen 1
        param[0][0][0].expectKind {nnkIdent, nnkSym}
        result.attrs.add nnkExprColonExpr.newTree(
          param[0][0][0],
          quote do: (`val`, true)
        )

      else:
        let attr = param[0].unquote
        attr.expectKind {nnkIdent, nnkSym}
        result.attrs.add nnkExprColonExpr.newTree(
          attr,
          if bindable: quote do: (`val`, false)
          else: val
        )
  
  else: result.callee = call

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
  let (callee, attrs, handlers) = destructureCall(call, bindable=false)
  if len(handlers) > 0:
    for handler in handlers: error "components dont have event handlers", handler[0]
  callee.expectKind {nnkIdent, nnkSym}
  result = newCall(bindSym"newTemplComponent", callee, attrs)
  if body.kind != nnkEmpty:
    result.add body.denestStmtList

proc newTemplSlotImpl(slot: NimNode, body = newEmptyNode()): NimNode =
  let (slot, body) = cosiderCommandSyntax(slot, body)
  slot.expectKind {nnkIdent, nnkSym}
  result = newCall(bindSym"newTemplSlot", newLit(slot.strVal))
  if body.kind != nnkEmpty:
    result.add body.denestStmtList

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

  macro `<..>`(call: untyped) {.inject.} =
    newTemplSlotImpl(call)

  macro `<..>`(call, body: untyped) {.inject.} =
    newTemplSlotImpl(call, body)

  block blockLabel:
    templDef

macro html*(templDef: untyped) =
  newCall(bindSym"templToTypable", templDefLabel, templDef)


proc tupleDefToTable(tupleDef: NimNode): Table[string, NimNode] =
  assert tupleDef.kind == nnkTupleConstr
  for node in tupleDef:
    assert node.kind == nnkExprColonExpr
    result[nimIdentNormalize($node[0])] = node[1]

proc tupleDefToTableAttrs(tupleDef: NimNode): Table[string, (NimNode, bool)] =
  assert tupleDef.kind == nnkTupleConstr
  for node in tupleDef:
    assert node.kind == nnkExprColonExpr
    assert node[1].kind == nnkTupleConstr
    assert len(node[1]) == 2
    assert node[1][1].kind in {nnkIdent, nnkSym}
    result[nimIdentNormalize($node[0])] = (node[1][0], parseBool($node[1][1]))

proc parseTempl*(node: NimNode): Templ =
  for node in node.denestStmtList.undoHiddenNodes:
    var elem = TemplElem(sym: genSym(nskVar, "elem"))

    case node.kind
    of nnkCall:
      case $node[0]
      of "newTemplText":
        assert len(node) == 2
        elem.kind = templText
        elem.text = node[1]

      of "newTemplTag":
        assert len(node) == 5
        elem.kind = templTag
        assert node[1].kind == nnkStrLit
        elem.tag = node[1].strVal
        elem.attrs = tupleDefToTableAttrs(node[2])
        for event, action in tupleDefToTable(node[3]):
          assert action.kind == nnkLambda
          elem.handlers[event] = action[6]
        if node[4].kind != nnkEmpty:
          assert node[4].kind == nnkLambda
          elem.childs = parseTempl(node[4][6])

      of "newTemplComponent":
        assert len(node) == 4
        elem.kind = templComponent
        elem.component = node[1]
        elem.params = tupleDefToTable(node[2])
        if node[3].kind != nnkEmpty:
          assert node[3].kind == nnkLambda
          let slots = node[3][6].denestStmtList
          if slots[0].kind == nnkCall and $slots[0][0] == "newTemplSlot":
            for slot in slots:
              slot.expectKind nnkCall
              assert $slot[0] == "newTemplSlot"
              assert slot[1].kind == nnkStrLit
              let slotName = slot[1].strVal
              assert slot[2].kind == nnkLambda
              assert slotName notin elem.slots
              elem.slots[slotName] = parseTempl(slot[2][6])
          else:
            elem.slots["_"] = parseTempl(slots)

      of "newTemplSlot":
        assert len(node) == 3
        elem.kind = templSlot
        assert node[1].kind == nnkStrLit
        elem.slotName = node[1].strVal
        node[2].expectKind nnkEmpty  #TODO slot defaults


    of nnkForStmt:
      elem.kind = templFor
      elem.forComponent = genSym(nskLet, "forComponent")
      elem.forBody.add parseTempl(node[^1])
      elem.forHead = node
      elem.forHead[^1] = newEmptyNode()

    else: assert false

    result.add elem