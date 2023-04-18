#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, strutils]


func `=~=`*(a,b: string): bool = cmpIgnoreStyle(a, b) == 0


func denestStmtList*(node: NimNode): NimNode =
  if node.kind == nnkStmtList:
    result = node
    while len(result) == 1 and result[0].kind == nnkStmtList:
      result = result[0]
  else:
    result = newStmtList(node)


iterator getFieldIdentsNodes*(T: NimNode): NimNode =
  var td = T.getType[1]
  if td.kind == nnkBracketExpr and $td[0] == "ref":
    td = td[1]
  for defs in td.getTypeImpl[2]:
    for sym in defs[0 ..< ^2]:
      yield sym

macro getFieldNames*(T: typedesc[object | ref object]): seq[string] =
  result = nnkBracket.newTree()
  for sym in getFieldIdentsNodes(T):
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