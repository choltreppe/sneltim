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
  PatchRef*[T] = ref object
    val: ref T
    prevVal: T
    patchProcs: seq[proc()]

func new[T](v: T): ref T =
  new result
  result[] = v

func newPatchRef[T](val: T): PatchRef[T] =
  new result
  result.val = new val

proc patch(pr: PatchRef, init = false) =
  if pr.val[] != pr.prevVal or init:
    debugEcho "patch: ", pr.val[]
    let l = len(pr.patchProcs)
    for i in 0 ..< l: pr.patchProcs[i]()
    pr.prevVal = pr.val[]


type
  Members = concept m
    m is tuple
    for f in m.fields:
      f is PatchRef

  ComponentInstance[M: Members] = object
    init: proc()
    mount: proc(parent: Node, getHook: proc: Node)
    detach: proc()
    pubMembers: M
    getFirstNode: proc: Node

  ComponentInstanceSeq[M: Members] = object
    instances: seq[ComponentInstance[M]]
    getFirstNode: proc: Node

  Component*[M: Members] = proc: ComponentInstance[M]

func newComponentInstance[M: Members](pubMembers: M): ComponentInstance[M] =
  result.pubMembers = pubMembers


proc componentImpl(
  inputInitSection: NimNode,
  templ: Templ,
  inheritMembers = newSeq[NimNode]()
): NimNode =

  type
    MemberRefKind = enum refmRead, refmMut
    MemberRefs = array[MemberRefKind, seq[int]]

  func add(a: var MemberRefs, b: MemberRefs) =
    for kind in MemberRefKind:
      a[kind].add b[kind]

  var
    members = inheritMembers
    procMemberRefs: seq[tuple[sym: NimNode, refs: MemberRefs]]

  proc findMemberRefs(node: NimNode): MemberRefs =
    let node = node.undoHiddenNodes
    case node.kind
    of nnkSym:
      if (let i = members.findIt(node, it[0]); i >= 0):
        result[refmRead].add i

    of nnkCall, nnkCommand:
      if (let i = procMemberRefs.findIt(node, it[0]); i >= 0):
        result.add procMemberRefs[i][1]
      let tds = node[0].getType[2..^1]
      for sym in node[1..^1]:
        if (let i = members.findIt(sym, it[0]); i >= 0):
          result[refmRead].add i
          let td = tds[i]
          if td.kind == nnkBracketExpr and td[0].kind == nnkSym and $td[0] == "var":
            result[refmMut].add i

    of nnkAsgn:
      if (let i = members.findIt(node[0], it[0]); i >= 0):
        result[refmMut].add i
      result.add findMemberRefs(node[1])

    of AtomicNodes - {nnkSym}: discard

    else:
      for node in node:
        result.add findMemberRefs(node)

  var
    initSection = newStmtList()
    pubMembers = nnkTupleConstr.newTree()

  proc scanBody(node: NimNode) =
    for node in node.denestStmtList:
      case node.kind
      of nnkStmtList, nnkStmtListExpr: scanBody node

      of nnkVarSection, nnkLetSection:
        let isVar = node.kind == nnkVarSection

        for defs in node:
          let defaultVal =
            if defs[^1].kind == nnkEmpty:
              newCall(bindSym"default", defs[^2].unbindSyms)
            else: defs[^1]
          for sym in defs[0 ..< ^2]:
            let ident = ident($sym)
            if not (sym.isExported or isVar):
              initSection.add: quote do:
                let `ident` = `defaultVal`
            else:
              members.add ident
              initSection.add: quote do:
                let `ident` = newPatchRef(`defaultVal`)
              if sym.isExported:
                pubMembers.add newColonExpr(ident, ident)

      of nnkProcDef, nnkFuncDef:
        procMemberRefs.add (node[0], findMemberRefs(node))

      else:
        initSection.add node

  scanBody inputInitSection.undoHiddenNodes

  result = quote do:
    proc: auto =
      `initSection`
      newComponentInstance(`pubMembers`)

  debugEcho result.repr


macro component*(componentDef: typed): Component =

  var
    initSection = newStmtList()
    templDef: NimNode

  proc scanBody(node: NimNode) =
    for node in node.denestStmtList.undoHiddenNodes:
      case node.kind
      of nnkStmtList, nnkStmtListExpr: scanBody node

      of nnkMacroDef, nnkTemplateDef: discard

      elif node.kind in {nnkBlockStmt, nnkBlockExpr} and node[0] == templDefLabel:
        if templDef != nil:
          error "html template already defined", node
        templDef = node[1]

      else: initSection.add node
  
  scanBody componentDef

  if templDef == nil:
    error "no html template defined", componentDef
  let templ = parseTempl(templDef)

  componentImpl(initSection, templ)
