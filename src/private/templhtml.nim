#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, sequtils, strutils, strformat, parseutils, setutils, tables]
import /home/joel/daten/programming/nim/parlexgen/src/parlexgen


type
  ValKind* = enum valStr, valCode
  Val* = object
    case kind*: ValKind
    of valStr: str*: string
    of valCode: code*: NimNode

  TemplText* = seq[Val]

  TemplElemKind* = enum templText, templTag, templComponent, templFor
  TemplElem* = ref object
    case kind*: TemplElemKind
    of templText:
      text*: TemplText
    of templTag:
      tag*: string
      attrs*: Table[string, Val]
      handlers*: Table[string, NimNode]
      childs*: seq[TemplElem]
    of templComponent:
      component*: NimNode
      vars*: Table[string, NimNode]
      componentBody*: seq[TemplElem]
    of templFor:
      forHead*: NimNode
      forBody*: string

  Templ* = seq[TemplElem]

func `$`*(elems: Templ): string

func `$`*(elem: TemplElem): string =
  case elem.kind
  of templText:
    for val in elem.text:
      result.add:
        case val.kind
        of valStr: val.str
        of valCode: "{" & repr(val.code) & "}"

  of templTag:
    result = "<" & elem.tag
    for name, val in elem.attrs:
      result &= fmt " {name}="
      result.add:
        case val.kind
        of valStr: '"' & val.str & '"'
        of valCode: '{' & repr(val.code) & '}'
    for name, code in elem.handlers:
      result &= fmt" on:{name}={{{repr code}}}"
    if len(elem.childs) == 0:
      result &= "/>"
    else:
      result &= fmt ">\n{elem.childs}</>"

  of templComponent:
    result = "<{" & repr(elem.component) & "}"
    for name, val in elem.vars:
      result &= fmt" {name}={{{repr val}}}"
    result &= "/>"

  of templFor:
    result = fmt "{{% {repr elem.forHead} %}}\n{elem.forBody}{{% endfor %}}"

  result &= '\n'


func `$`*(elems: Templ): string =
  for elem in elems:
    result &= $elem

func newVal(s: string):  Val = Val(kind: valStr,  str: s)
func newVal(n: NimNode): Val = Val(kind: valCode, code: n)

func merge[T: Table](a, b: T): T =
  result = a
  for k, v in b: result[k] = v

func startsWith(s,prefix: string, start: int): bool =
  let prefixLen = len(prefix)
  let sLen = len(s)
  var i = 0
  var j = start
  while true:
    if i >= prefixLen: return true
    if j >= sLen or s[j] != prefix[i]: return false
    inc i
    inc j

func parseUntilEscaped(s: string, v: var string, c: set[char], start = 0): int =
  var i = start
  while i < len(s) and s[i] notin c:
    if s[i] == '\\': inc i
    v &= s[i]
    inc i
  i - start


func parseTempl*(code: string): Templ =
  var i = 0

  proc skipSpaces =
    i += code.skipWhitespace(i)

  proc parseCodeBlock(asBlock = true): NimNode =
    assert code[i] == '{'
    inc i
    let start = i
    var nestingDepth = 1
    while nestingDepth > 0:
      case code[i]
      of '{': inc nestingDepth
      of '}': dec nestingDepth
      else: discard
      inc i
    let codeStr = code[start ..< i-1].dedent
    if asBlock:
      nnkBlockStmt.newTree(newEmptyNode(),
        newStmtList(parseStmt(codeStr))
      )
    else: parseExpr(codeStr)


  proc parseElem: TemplElem =
    new result
    if code[i] == '<':
      inc i
      skipSpaces()

      if code[i] == '{':
        result.kind = templComponent
        result.component = parseCodeBlock(false)
        while true:
          skipSpaces()

          if code[i] == '/':
            inc i
            skipSpaces()
            assert code[i] == '>'
            inc i
            return
          
          var name: string
          i += code.parseUntil(name, '=', i)
          name = strip(name)
          inc i
          skipSpaces()
          result.vars[name] = parseCodeBlock(false)

      else:
        result.kind = templTag
        i += code.parseUntil(result.tag, {' ', '/', '>'}, i)
        while true:
          skipSpaces()

          if code[i] == '>':
            inc i
            break
          if code[i] == '/':
            inc i
            skipSpaces()
            assert code[i] == '>'
            inc i
            return

          var name: string
          i += code.parseUntil(name, '=', i)
          name = strip(name)
          inc i
          skipSpaces()

          let val =
            case code[i]
            of '{':
              newVal(parseCodeBlock())
            of '"':
              inc i
              var str: string
              i += code.parseUntilEscaped(str, {'"'}, i)
              inc i
              newVal(str)
            else:
              assert false  #TODO: err msg
              return

          if name.startsWith("on:"):
            assert val.kind == valCode  #TODO: err msg
            result.handlers[name[3..^1]] = val.code
          else:
            result.attrs[name] = val

        while true:
          if code[i] == '<':
            var j = i + 1
            j += code.skipWhitespace(j)
            if code[j] == '/':
              i = j + 1
              var tag: string
              i += code.parseUntil(tag, '>', i)
              inc i
              tag = strip(tag)
              assert tag == "" or tag == result.tag  #TODO: err msg
              return

          result.childs &= parseElem()

    elif code.startsWith("{%", i):
      i += 2
      skipSpaces()
      if code.startsWith("for", i):
        result.kind = templFor
        var headStr: string
        i += code.parseUntil(headStr, "%}", i)
        result.forHead = parseExpr(headStr & ": discard")
        i += 2
        i += code.parseUntil(result.forBody, "{%", i)
        i += 2
        skipSpaces()
        if code[i] == '}': inc i
        else:
          assert code.startsWith("endfor", i)  #TODO: err msg
          i += 6
          skipSpaces()
          assert code.startsWith("%}", i)  #TODO: err msg
          i += 2 

      else: assert false #TODO: err msg

    else:
      result.kind = templText
      while i < len(code) and code[i] != '<' and not code.startsWith("{%", i):
        result.text.add:
          if code[i] == '{':
            newVal(parseCodeBlock())
          else:
            var text: string
            i += code.parseUntilEscaped(text, {'{', '<'}, i)
            newVal(text)

  while i < len(code):
    result &= parseElem()


#[func parseTempl*(code: string): TemplHtml =

  type
    TokenKind = enum IDENT, STR, INCURL, LANGLE="<", RANGLE=">", SLASH="/", EQ="=", COLON=":"
    Token = object
      case kind: TokenKind
      of IDENT, STR, INCURL: strVal: string
      else: discard

  func allCharsBut(but: set[char]): string =
    "[" & complement(but + {'[', ']', '\n', '\r', '\0'}).toSeq.join & r"\[\]]"

  makeLexer lex[Token]:
    r"[a-zA-Z\_\-][a-zA-Z0-9\_\-]*": Token(kind: IDENT, strVal: match)
    ("\\\"" & allCharsBut({'"'}) & "*\\\""): Token(kind: STR, strVal: match)
    (r"\{" & allCharsBut({'{','}'}) & r"*\}"): Token(kind: INCURL, strVal: match)
    for k in LANGLE..COLON:
      ("\\" & $k): Token(kind: k)

    r"\s+": discard

  makeParser parse[Token]:

    elem[TemplHtml]:
      (LANGLE, IDENT, args, SLASH, RANGLE):
        TemplHtml(
          kind: templTag,
          tag: s[1].strVal,
          attrs: s[2].attrs,
          handlers: s[2].handlers
        )
      
      (LANGLE, IDENT, args, RANGLE, elems, LANGLE, SLASH, IDENT, RANGLE):
        assert s[1].strVal == s[7].strVal
        TemplHtml(
          kind: templTag,
          tag: s[1].strVal,
          attrs: s[2].attrs,
          handlers: s[2].handlers,
          childs: s[4]
        )

    args[tuple[attrs: Attrs, handlers: Handlers]]:
      (arg, args):
        (
          merge(s[0].attrs, s[1].attrs),
          merge(s[0].handlers, s[1].handlers)
        )
      (): (newAttrs(), newHandlers())

    arg[tuple[attrs: Attrs, handlers: Handlers]]:
      (IDENT, EQ, STR):    ({s[0].strVal: (attrLit,  s[2].strVal)}.toTable, newHandlers())
      (IDENT, EQ, INCURL): ({s[0].strVal: (attrCode, s[2].strVal)}.toTable, newHandlers())
      (IDENT, COLON, IDENT, EQ, INCURL):
        assert s[0].strVal == "on"
        (newAttrs(), {s[1].strVal: s[3].strVal}.toTable)

    elems[seq[TemplHtml]]:
      (elem, elems): s[0] & s[1]
      (): @[]

  try:
    return parse(code, lex)
  
  except LexingError as e: debugEcho e.line, " ", e.col]#