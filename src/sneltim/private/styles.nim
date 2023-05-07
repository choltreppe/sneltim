#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, strutils, tables]
import ./utils
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

  Selector* = object
    case kind*: SelectorKind
    of pseudoClass: class*: PseudoClass
    of pseudoElem: elem*: PseudoElem
    childs*: Style

  Style* = ref object
    attrs*: OrderedTable[string, string]
    selectors*: seq[Selector]

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





macro newStyle*(body: untyped): Style =

  proc parseAttrNameTempl(node: NimNode): NimNode =
    case node.kind
    of nnkPar: parseAttrNameTempl(node[0])
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

  proc parseStyle(node: NimNode): NimNode =
    let style = genSym(nskVar, "style")

    proc parseBody(node: NimNode): NimNode =
      result = newStmtList()
      for node in node.denestStmtList:
        result.add:
          case node.kind
          of nnkCall:
            node.expectLen 2
            let name = parseAttrNameTempl(node[0])
            let val = node[1]
            quote do:
              `style`.attrs[`name`] = $`val`

          of nnkPrefix:
            node.expectLen 3
            let name = node[1]

            proc addSelector(kind: SelectorKind, fieldName: string): NimNode =
              let field = ident(fieldName)
              let childs = parseStyle(node[2])
              quote do:
                `style`.selectors.add Selector(
                  kind: `kind`,
                  `field`: `name`,
                  childs: `childs`
                )

            case $node[0]
            of "-:":  addSelector(pseudoClass, "class")
            of "-::": addSelector(pseudoElem , "elem" )

            of "-@":
              name.expectKind {nnkIdent, nnkSym}
              let cmd = $name
              let extend = node[2]
              case cmd
              of "extend":
                quote do:
                  `style`.merge `extend`

              else:
                error "unknown comand '"&cmd&"'", name
                break

            else:
              error "unexpected '" & $node[0] & "'", node[0]
              break

          of nnkLetSection, nnkVarSection: node

          of nnkForStmt:
            node[^1] = parseBody(node[^1])
            node

          of nnkIfStmt:
            for branch in node:
              branch[^1] = parseBody(branch[^1])
            node

          of nnkCaseStmt:
            for branch in node[1..^1]:
              branch[^1] = parseBody(branch[^1])
            node

          else:
            error "unexpected", node
            break

    let body = parseBody(node)
    quote do:
      var `style` = Style()
      `body`
      `style`

  result = parseStyle(body)
  debugEcho result.repr
