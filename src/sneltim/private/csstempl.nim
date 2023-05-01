import std/[macros, options, sequtils, strutils, strformat]
import fusion/matching

import ./utils


type
  InterpolatedElem = object
    case isInterpolate: bool
    of true: val: NimNode
    else: str: string
  Interpolated = seq[InterpolatedElem]

  SelectorOp = enum
    selectOpChild=">", selectOpChildRec="",
    selectOpSucc="+", selectOpSuccRec="~"

  SelectorPseudoClass = object
    name: string
    arg: Option[NimNode]

  SelectorAttribute = object
    name: string
    case matchVal: bool
    of true:
      op: string
      val: NimNode
    else: discard

  SelectorModifierKind = enum modPseudoClass, modAttribute
  SelectorModifier = object
    case kind: SelectorModifierKind
    of modPseudoClass: pseudoClass: SelectorPseudoClass
    of modAttribute:   attribute:   SelectorAttribute

  SelectorElemKind = enum selectWildcard, selectTag, selectId, selectClass

  SelectorElem = object
    case kind: SelectorElemKind
    of selectWildcard: discard
    of selectTag: tag: string
    of selectId, selectClass: name: NimNode
    modifier: seq[SelectorModifier]

  SelectorPathNode = object
    op: SelectorOp
    elem: SelectorElem

  SelectorPath = seq[SelectorPathNode]

  Selector = seq[SelectorPath]

func `$`*(interp: Interpolated): string =
  for elem in interp:
    result.add:
      if elem.isInterpolate: &"${{{elem.val.repr}}}"
      else: elem.str

func `$`*(pseudoClass: SelectorPseudoClass): string =
  result = ":" & pseudoClass.name
  if Some(@arg) ?= pseudoClass.arg:
    result.add &"({arg.repr})"

func `$`*(attr: SelectorAttribute): string =
  result = "[" & attr.name
  if attr.matchVal:
    result.add &" {attr.op} {attr.val.repr}"
  result.add "]"

func `$`*(modifier: SelectorModifier): string =
  case modifier.kind
  of modPseudoClass: $modifier.pseudoClass
  of modAttribute:   $modifier.attribute

func `$`*(elem: SelectorElem): string =
  result =
    case elem.kind
    of selectWildcard: "*"
    of selectTag: elem.tag
    of selectId: &"#{elem.name.repr}"
    of selectClass: &".{elem.name.repr}"
  for modifier in elem.modifier:
    result.add $modifier

func `$`*(pathNode: SelectorPathNode): string =
  &"{pathNode.op} {pathNode.elem}"

func `$`*(path: SelectorPath): string =
  path.mapIt($it).join(" ")

func `$`*(selector: Selector): string =
  selector.mapIt($it).join(", ")

func asModifier(pseudoClass: SelectorPseudoClass): SelectorModifier =
  result.kind = modPseudoClass
  result.pseudoClass = pseudoClass

func asModifier(attribute: SelectorAttribute): SelectorModifier =
  result.kind = modAttribute
  result.attribute = attribute


func parseSelector*(body: NimNode): Selector =
  func parseInterpolated(node: NimNode): Interpolated =
    discard #TODO

  func parseOp(node: NimNode): SelectorOp =
    assert node.kind in {nnkIdent, nnkSym}
    case $node
    of ">": selectOpChild
    of "..>": selectOpChildRec
    of "+": selectOpSucc
    of "~": selectOpSuccRec
    else:
      error &"invalid {node}", node
      return

  func parseAttribute(node: NimNode): SelectorAttribute =
    case node.kind
    of nnkIdent, nnkSym:
      SelectorAttribute(name: $node, matchVal: false)
    of nnkInfix:
      node[1].expectKind {nnkIdent, nnkSym}
      SelectorAttribute(
        name: $node[1],
        matchVal: true,
        op: $node[0],
        val: node[2]
      )
    of nnkExprEqExpr:
      node[0].expectKind {nnkIdent, nnkSym}
      SelectorAttribute(
        name: $node[0],
        matchVal: true,
        op: "=",
        val: node[1]
      )
    else:
      error "invalid attribute selector", node
      return


  func parseElem(node: NimNode, modifier = newSeq[SelectorModifier]()): SelectorElem =
    let node = node.unquote

    case node.kind
    of nnkDotExpr:
      node[1].expectKind nnkIdent
      parseElem(
        node[0],
        SelectorPseudoClass(name: $node[1]).asModifier &
        modifier
      )

    of nnkIdent, nnkSym:
      let name = $node
      if name == "_":
        SelectorElem(kind: selectWildcard, modifier: modifier)
      else:
        SelectorElem(kind: selectTag, tag: name, modifier: modifier)

    of nnkCall, nnkCommand, nnkCallStrLit:
      if node[0].kind == nnkOpenSymChoice and $node[0] == "[]":
        node.expectLen 3
        parseElem(node[1], parseAttribute(node[2]).asModifier & modifier)

      else:
        node.expectLen 2
        if node[0].kind == nnkDotExpr:
          parseElem(
            node[0][0],
            SelectorPseudoClass(name: $node[0][1], arg: some(node[1])).asModifier &
            modifier
          )

        else:
          node[0].expectKind {nnkIdent, nnkSym}
          var res = SelectorElem(kind:
            case $node[0]
            of "id": selectId
            of "class": selectClass
            else:
              error "invalid selector", node
              return
          )
          res.name = node[1]
          res

    of nnkBracketExpr:
      node.expectLen 2
      parseElem(node[0], parseAttribute(node[1]).asModifier & modifier)

    else:
      error "invalid selector", node
      return

  func parsePatch(node: NimNode, op = none(SelectorOp)): SelectorPath =
    case node.kind
    of nnkInfix:
      parsePatch(node[1], op) &
      parsePatch(node[2], some(parseOp(node[0])))

    of nnkPrefix:
      if op.isSome:
        error &"invalid {node[0]}", node[0]
        return
      else:
        parsePatch(node[1], some(parseOp(node[0])))

    else:
      @[SelectorPathNode(
        elem: parseElem(node),
        op: if Some(@op) ?= op: op
            else: selectOpChildRec
      )]

  body.expectKind nnkBracket
  for node in body:
    result.add parsePatch(node)