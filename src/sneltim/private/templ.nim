#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, sequtils, strutils, strformat, tables, options]
import fusion/matching
import ./utils, ./styles
export styles


type
  TemplElemKind* = enum templText, templTag, templComponent, templSlot, templFor, templIfCase
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
      style*: Option[tuple[sym,def: NimNode]]

    of templComponent:
      component*: NimNode
      params*: Table[string, NimNode]
      slots*: Table[string, Templ]

    of templSlot:
      slotName*: string

    of templFor:
      forHead*: NimNode
      forBody*: Templ
      forComponentSym*: NimNode

    of templIfCase:
      case isCaseStmt*: bool
      of true:
        caseHead*: NimNode
        ofBranches*: seq[tuple[matches: seq[NimNode], body: Templ]]
      else: discard
      elifBranches*: seq[tuple[cond: NimNode, defs: seq[NimNode], body: Templ]]
      elseBody*: Option[Templ]

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
      result.add ">\n"
      let subIndentStr = " ".repeat(indent+1)
      for name, body in elem.slots:
        result.add &"{subIndentStr}<..{name}>\n"
        result.add `$`(body, indent+2)
        result.add &"{subIndentStr}</..{name}>\n"
      result.add indentStr & "</%>"

    of templSlot:
      result.add fmt"<..{elem.slotName}>"

    of templFor:
      result.add "for " &
        elem.forHead[0 ..< ^2].mapIt(it.repr).join(", ") &
        " in " & elem.forHead[^2].repr & ":\n"
      result.add `$`(elem.forBody, indent+1)

    of templIfCase:
      if elem.isCaseStmt:
        result.add &"case {elem.caseHead.repr}\n"
        for (matches, body) in elem.ofBranches:
          result.add "of " & matches.mapIt(it.repr).join(", ") & ":\n"
          result.add `$`(body, indent+1)
      for i, (cond, _, body) in elem.elifBranches:
        result.add:
          if not elem.isCaseStmt and i == 0: "if"
          else: "elif"
        result.add &" {cond.repr}:\n"
        result.add `$`(body, indent+1)
      if Some(@body) ?= elem.elseBody:
        result.add &"else:\n" & `$`(body, indent+1)

    if elem.kind notin {templFor}:
      result.add "\n"


proc newTemplText*(s: string) = discard
proc newTemplTag*(name: string, params,handlers: tuple, style: Option[Style], content: proc = nil) = discard
proc newTemplComponent*(component: proc, params: tuple, content: proc = nil) = discard
proc newTemplSlot*(name: string, content: proc = nil) = discard
proc newTemplSlotDef*(name: string, content: proc()) = discard

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

proc extractStyleDef(body: NimNode): tuple[body, styleDef: NimNode] =
  result.body = newStmtList()
  for stmt in body.denestStmtList:
    if stmt.kind == nnkCall and stmt[0].kind in {nnkIdent, nnkSym} and cmpIgnoreStyle($stmt[0], "style") == 0:
      stmt.expectLen 2
      if result.styleDef != nil:
        error "cant define multiple styles for one element", stmt
      result.styleDef = stmt[1]
    elif stmt.kind != nnkEmpty:
      result.body.add stmt
  result.styleDef =
    if result.styleDef == nil:
      quote do: none(Style)
    else:
      let styleDef = result.styleDef
      quote do: some(newStyle(`styleDef`))

proc newTemplTagImpl(call: NimNode, body = newEmptyNode()): NimNode =
  let (callee, attrs, handlers) = destructureCall(call)
  callee.expectKind {nnkIdent, nnkSym}
  let (body, styleDef) = extractStyleDef(body)
  result = newCall(bindSym"newTemplTag", newLit($callee), attrs, handlers, styleDef)
  if len(body) > 0:
    assert body.kind == nnkStmtList
    result.add: quote do:
      proc = `body`

proc newTemplComponentImpl(call: NimNode, body = newEmptyNode()): NimNode =
  let (callee, attrs, handlers) = destructureCall(call, bindable=false)
  if len(handlers) > 0:
    for handler in handlers: error "components dont have event handlers", handler[0]
  #callee.expectKind {nnkIdent, nnkSym}
  result = newCall(bindSym"newTemplComponent", callee, attrs)
  if body.kind != nnkEmpty:
    assert body.kind == nnkStmtList
    result.add: quote do:
      proc = `body`

proc newTemplSlotImpl(slot: NimNode, body = newEmptyNode()): NimNode =
  slot.expectKind {nnkIdent, nnkSym}
  result = newCall(bindSym"newTemplSlot", newLit(slot.strVal))
  if body.kind != nnkEmpty:
    assert body.kind == nnkStmtList
    result.add: quote do:
      proc = `body`

proc newTemplSlotDefImpl(slot, body: NimNode): NimNode =
  slot.expectKind {nnkIdent, nnkSym}
  newCall(bindSym"newTemplSlotDef", newLit(slot.strVal), body.denestStmtList)

macro html*(body: untyped) =
  proc toProcCalls(node: NimNode): NimNode =
    proc stmtToProcCall(node: NimNode): NimNode =
      case node.kind
      of nnkCall, nnkCommand, nnkPrefix:
        node[0].expectKind {nnkIdent, nnkSym}
        node.expectLen 2, 3

        var (head, body) = cosiderCommandSyntax(
          node[1],
          if len(node) == 2: newEmptyNode()
          else: node[2]
        )
        if body.kind != nnkEmpty:
          body = body.toProcCalls

        case ($node[0]).nimIdentNormalize
        of "text":
          body.expectKind nnkEmpty
          newTemplTextImpl(head)
        of "<>": newTemplTagImpl(head, body)
        of "<%>": newTemplComponentImpl(head, body)
        of "<..>": newTemplSlotImpl(head, body)
        of "<=>": newTemplSlotDefImpl(head, body)
        else: node

      of AtomicNodes: node
      else: node.map(toProcCalls)

    if node.kind == nnkStmtList:
      node.map(stmtToProcCall)
    else:
      node.stmtToProcCall

  nnkBlockStmt.newTree(templDefLabel, body.toProcCalls)


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
        assert len(node) == 6
        elem.kind = templTag
        assert node[1].kind == nnkStrLit
        elem.tag = node[1].strVal

        elem.attrs = tupleDefToTableAttrs(node[2])

        for event, action in tupleDefToTable(node[3]):
          assert action.kind == nnkLambda
          elem.handlers[event] = action[6]

        assert node[4].kind == nnkCall
        assert node[4][0].kind in {nnkSym, nnkOpenSymChoice}
        if $node[4][0] == "some":
          elem.style = some((genSym(nskLet, "style"), node[4][1].removeMacroDefs))

        if node[5].kind != nnkEmpty:
          assert node[5].kind == nnkLambda
          elem.childs = parseTempl(node[5][6])

      of "newTemplComponent":
        assert len(node) == 4
        elem.kind = templComponent
        elem.component = node[1]
        elem.params = tupleDefToTable(node[2])
        if node[3].kind != nnkEmpty:
          assert node[3].kind == nnkLambda
          let slots = node[3][6].denestStmtList
          if slots[0].kind == nnkCall and $slots[0][0] == "newTemplSlotDef":
            for slot in slots:
              slot.expectKind nnkCall
              assert $slot[0] == "newTemplSlotDef"
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
      elem.forComponentSym = genSym(nskLet, "forComponent")
      elem.forBody.add parseTempl(node[^1])
      elem.forHead = node
      elem.forHead[^1] = newEmptyNode()

    of nnkIfStmt, nnkCaseStmt:
      elem.kind = templIfCase
      elem.isCaseStmt = node.kind == nnkCaseStmt
      let branches =
        if elem.isCaseStmt:
          elem.caseHead = node[0]
          node[1..^1]
        else:
          node[0..^1]
      for branch in branches:
        case branch.kind
        of nnkOfBranch:
          elem.ofBranches.add (branch[0 ..< ^1], parseTempl(branch[^1]))
        of nnkElifBranch:
          elem.elifBranches.add (branch[0], getIfCondDefs(branch[0]), parseTempl(branch[1]))
        else:
          assert branch.kind == nnkElse
          assert elem.elseBody.isNone
          elem.elseBody = some(parseTempl(branch[0]))

    of nnkEmpty: discard

    else: error "malformed html template", node

    result.add elem