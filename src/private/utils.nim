#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros]


func denestStmtList*(node: NimNode): NimNode =
  if node.kind == nnkStmtList:
    result = node
    while len(result) == 1 and result[0].kind == nnkStmtList:
      result = result[0]
  else:
    result = newStmtList(node)

macro getFieldNames*(T: typedesc[object | ref object]): seq[string] =
  result = nnkBracket.newTree()
  var td = T.getType[1]
  if td.kind == nnkBracketExpr and $td[0] == "ref":
    td = td[1]
  for defs in td.getTypeImpl[2]:
    for sym in defs[0 ..< ^2]:
      result &= newLit($sym)
  result = result.prefix("@")