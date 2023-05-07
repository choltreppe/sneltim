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


proc map*(node: NimNode, f: proc(x: NimNode): NimNode): NimNode =
  assert node.kind notin AtomicNodes
  result = node.kind.newTree()
  for node in node:
    result.add f(node)

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

func removeMacroDefs*(node: NimNode): NimNode =
  case node.kind
  of nnkMacroDef, nnkTemplateDef: result = newStmtList()
  of AtomicNodes: result = node
  else:
    result = node.kind.newTree()
    for node in node:
      result.add node.removeMacroDefs

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

# get vars/lets defined inside of condition
func getIfCondDefs*(node: NimNode): seq[NimNode] =
  case node.kind
  of nnkStmtListExpr:
    for stmt in node:
      if stmt.kind in {nnkLetSection, nnkVarSection}:
        for defs in stmt:
          if defs.kind in {nnkIdentDefs, nnkVarTuple}:
            for sym in defs[0 ..< ^2]:
              if $sym != "_":
                result.add sym

  of AtomicNodes: discard
  else:
    for node in node:
      result.add getIfCondDefs(node)


func isVarType*(td: NimNode): bool =
  td.kind == nnkVarTy or
  td.kind == nnkBracketExpr and td[0].kind == nnkSym and $td[0] == "var"

func isVar*(node: NimNode): bool =
  node.getTypeInst.isVarType

func paramsVar*(node: NimNode): seq[bool] =
  for td in node.getType[2..^1]:
    result.add td.isVarType

func unVarType*(td: NimNode): NimNode =
  if td.kind == nnkVarTy:
    td[0]
  elif td.kind == nnkBracketExpr and td[0].kind == nnkSym and $td[0] == "var":
    td[1]
  elif td.kind in {nnkBracketExpr, nnkCommand} and td[0].kind == nnkSym and $td[0] == "lent":
    td[1]
  else:
    td