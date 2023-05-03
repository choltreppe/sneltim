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


template newStyle*(body: untyped): Style =
  block:

    var style = Style()
    var ctx = style

    proc setAttr(name, val: string) =
      ctx.attrs[name] = val

    macro `--`(name: untyped, val: string) =
      name.expectKind {nnkIdent, nnkSym}
      let name = nimIdentToCssAttr($name)
      newCall(bindSym"setAttr", newLit(nimIdentToCssAttr($name)), val)

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

    body
    style

template newStyleTempl*(body: untyped): StyleTempl =
  proc: Style = newStyle(body)