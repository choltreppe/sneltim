#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, genasts, typetraits, sequtils, strutils, setutils, sets, tables, dom, options, enumerate]
import fusion/matching
export sets, tables, dom, sequtils

import ./private/[templ, utils]
export templ.html


type
  PatchRef[T] = ref object
    val: ref T
    prevVal: T
    patchProcs: seq[proc()]


macro component*(body: typed): untyped =

  var templDef: NimNode

  proc scanBody(node: NimNode) =
    for node in node.denestStmtList.undoHiddenNodes:
      case node.kind
      of nnkStmtList, nnkStmtListExpr: scanBody node

      elif node.kind in {nnkBlockStmt, nnkBlockExpr} and node[0] == templDefLabel:
        if templDef != nil:
          error "html template already defined", node
        templDef = node[1]

      else: discard
  
  scanBody body

  if templDef == nil:
    error "no html template defined"
  let templ = parseTempl(templDef)

  debugEcho templ
