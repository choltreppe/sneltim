#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, strutils, tables]
export tables


type
  PseudoClass* = enum
    none,
    checked,
    disabled, enabled,
    empty,
    focus,
    hover,
    inRange, outOfRange,
    indeterminate,
    valid, invalid,
    link, visited,
    target,

  PseudoElem* = enum
    none,
    after, before,
    firstLetter, firstLine,
    marker, selection,
    placeholder

  SelectorKind = enum pseudoClass, pseudoElem

  Selector = object
    case kind: SelectorKind
    of pseudoClass: class: PseudoClass
    of pseudoElem: elem: PseudoElem
    childs: Style

  Style* = ref object
    attrs: OrderedTable[string, string]
    selectors: seq[Selector]

  StyleTempl* = proc: Style


func nimIdentToCssAttr(name: string): string =
  for c in name:
    if c.isUpperAscii:
      result.add '-' & c.toLowerAscii
    else:
      result.add c

func render*(style: Style, ctx: string): string =
  result.add ctx & "{"
  if len(style.attrs) > 0:
    for name, val in style.attrs:
      result.add name & ":" & val & ";"
  result.add "}\n"

  for selector in style.selectors:
    result.add render(
      selector.childs,
      ctx & (
        case selector.kind
        of pseudoClass: ":" & nimIdentToCssAttr($selector.class)
        of pseudoElem: "::" & nimIdentToCssAttr($selector.elem)
      )
    )


proc merge*(a: var Style, b: Style) =
  for name, val in b.attrs:
    a.attrs[name] = val
  a.selectors.add b.selectors

func merge*(a,b: Style): Style =
  result = a
  result.merge b


proc parseAttrNameTempl(node: NimNode): NimNode =
  case node.kind
  of nnkInfix:
    assert $node[0] == "-"
    infix(infix(
      parseAttrNameTempl(node[1]), "&",
      newLit"-"), "&",
      parseAttrNameTempl(node[2])
    )
  of nnkCurly:
    node.expectLen 1
    node[0]
  else:
    node.expectKind {nnkIdent, nnkSym}
    newLit(nimIdentToCssAttr($node))


template newStyle*(body: untyped): Style =
  block:

    var style = Style()
    var ctx = style

    proc setAttr(name, val: string) =
      ctx.attrs[name] = val

    macro `:=`(name: untyped, val: string) =
      newCall(bindSym"setAttr", parseAttrNameTempl(name), val)

    proc newPseudoClassCtx(classDef: PseudoClass) =
      let newCtx = Style()
      ctx.selectors.add Selector(kind: pseudoClass, class: classDef, childs: newCtx)
      ctx = newCtx

    template `-:`(classDef: PseudoClass, childsDef: untyped) =
      let oldCtx = ctx
      newPseudoClassCtx classDef
      childsDef
      ctx = oldCtx

    proc newPseudoElemCtx(elemDef: PseudoElem) =
      let newCtx = Style()
      ctx.selectors.add Selector(kind: pseudoElem, elem: elemDef, childs: newCtx)
      ctx = newCtx

    template `-::`(elemDef: PseudoElem, childsDef: untyped) =
      let oldCtx = ctx
      newPseudoElemCtx elemDef
      childsDef
      ctx = oldCtx

    proc extendStyle(extend: Style) =
      style.merge extend

    macro `-@`(name, val: untyped) =
      name.expectKind {nnkIdent, nnkSym}
      let cmd = $name
      case cmd
      of "extend":
        newCall(bindSym"extendStyle", val)

      else:
        error "unknown comand '"&cmd&"'", name
        return

    body
    style