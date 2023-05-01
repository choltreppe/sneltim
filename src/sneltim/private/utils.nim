#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, strutils, setutils]


func `=~=`*(a,b: string): bool = cmpIgnoreStyle(a, b) == 0


iterator revItems*[T](x: openarray[T]): T =
  for i in countdown(len(x)-1, 0):
    yield x[i]

template findIt*(container, elem, get: untyped): untyped =
  var res = -1
  var i = 0
  for it {.inject.} in container:
    if get == elem:
      res = i
      break
    inc i
  res

func denestStmtList*(node: NimNode): NimNode =
  if node.kind == nnkStmtList:
    result = node
    while len(result) == 1 and result[0].kind == nnkStmtList:
      result = result[0]
  else:
    result = newStmtList(node)

func unquote*(node: NimNode): NimNode =
  if node.kind == nnkAccQuoted: node[0]
  else: node

# probably incomplete (i dont realy know the compiler internals)
func undoHiddenNodes*(node: NimNode): NimNode =
  case node.kind
  of nnkHiddenAddr, nnkHiddenDeref: undoHiddenNodes(node[0])
  of nnkHiddenStdConv: undoHiddenNodes(node[1])
  of AtomicNodes: node
  else:
    var res = node.kind.newTree()
    for node in node:
      res.add undoHiddenNodes(node)
    res

func unbindSyms*(node: NimNode): NimNode =
  case node.kind
  of nnkSym:
    result = ident($node)
  of complement(AtomicNodes):
    result = node.kind.newTree()
    for node in node:
      result.add unbindSyms(node)
  else:
    result = node
  

macro getFieldNames*(T: typedesc[tuple | ref tuple]): seq[string] =
  result = nnkBracket.newTree()
  var td = T.getType[1]
  if td.kind == nnkBracketExpr and $td[0] == "ref":
    td = td[1]
  for defs in td.getTypeImpl:
    for sym in defs[0 ..< ^2]:
      result &= newLit($sym)
  result = result.prefix("@")


func getForVars*(forStmt: NimNode): seq[NimNode] =
  forStmt.expectKind nnkForStmt
  template addVar(sym: NimNode) =
    if $sym != "_":
      result.add sym
  for node in forStmt[0 ..< ^2]:
    if node.kind == nnkVarTuple:
      for sym in node: addVar sym
    else: addVar node

func getIfCondBindings*(cond: NimNode): seq[NimNode] =
  if cond.kind == nnkStmtListExpr:
    for stmt in cond:
      if stmt.kind in {nnkLetSection, nnkVarSection}:
        for defs in stmt:
          if defs.kind in {nnkIdentDefs, nnkVarTuple}:
            for sym in defs[0 ..< ^2]:
              if $sym != "_":
                result.add sym


func isVarType(td: NimNode): bool =
  td.kind == nnkBracketExpr and td[0].kind == nnkSym and $td[0] == "var"

func isVar*(node: NimNode): bool =
  node.getType.isVarType

func paramsMut*(node: NimNode): seq[bool] =
  for td in node.getType[2..^1]:
    result.add td.isVarType