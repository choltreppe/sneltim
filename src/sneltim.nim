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
  PatchProcs = ref object
    procs: seq[PatchProcsNode]
  PatchProcsNode = object
    case isGroup: bool
    of true:
      group: PatchProcs
    of false:
      patchProc: proc()

  PatchRef[T] = ref object
    val: ref T
    prevVal: T
    patchProcs: PatchProcs

func new[T](v: T): ref T =
  new result
  result[] = v

func newPatchRef[T](val: T): PatchRef[T] =
  new result
  result.val = new val
  new result.patchProcs

func newPatchProc(p: proc()): PatchProcsNode =
  PatchProcsNode(isGroup: false, patchProc: p)

func newPatchProcGroup(g: PatchProcs): PatchProcsNode = 
  PatchProcsNode(isGroup: true, group: g)

proc patch(pps: PatchProcs, visited = newSeq[PatchProcs]()) =
  if pps notin visited:
    var i = 0
    while i < len(pps.procs):
      let pp = pps.procs[i]
      if pp.isGroup:
        patch pp.group, visited & pps
      else:
        pp.patchProc()
      inc i

proc patch(pr: PatchRef, init = false) =
  if pr.val[] != pr.prevVal or init:
    patch pr.patchProcs
    pr.prevVal = pr.val[]


type
  Members = concept ms
    ms is tuple
    for m in ms.fields:
      m is PatchRef

  ComponentInstance[M: Members] = object
    init: proc()
    mount: proc(parent: Node, getHook: proc: Node)
    detach: proc()
    pubMembers: M
    getFirstNode: proc: Node

  ComponentInstanceSeq[M: Members] = object
    instances: seq[ComponentInstance[M]]
    getHook: proc: Node

  Component*[M: Members] = proc: ComponentInstance[M]

template    instanceType[M](c: Component[M]): type =    ComponentInstance[M]
template instanceSeqType[M](c: Component[M]): type = ComponentInstanceSeq[M]

func newComponentInstance[M: Members](pubMembers: M): ComponentInstance[M] =
  result.pubMembers = pubMembers


func getFirstNode*(node: Node): Node {.inline.} = node

proc getFirstNode*(s: ComponentInstanceSeq): Node =
  if len(s.instances) > 0:
    s.instances[0].getFirstNode()
  else:
    s.getHook()


proc setAttrProperly*(node: Node, attr: string, val: auto) =
  let val = cstring($val)
  case attr
  of "value": node.value = val
  else: node.setAttr(attr, val)


proc componentImpl(
  inputInitSection: NimNode,
  templ: Templ,
  inheritMembers = newSeq[NimNode]()
): NimNode =

  # ---- members referencing analysis ----

  type
    MemberRefKind = enum refmAll, refmMut
    MemberRefs = array[MemberRefKind, seq[int]]

  func add(a: var MemberRefs, b: MemberRefs) =
    for kind in MemberRefKind:
      a[kind].add b[kind]

  var
    members = inheritMembers
    procMemberRefs: seq[tuple[sym: NimNode, refs: MemberRefs]]

  proc getMemberRefs(node: NimNode, varCtx = false): MemberRefs =
    let node = node.undoHiddenNodes
    case node.kind
    of nnkSym:
      if (let i = members.find(node); i >= 0):
        result[refmAll].add i
        if varCtx:
          result[refmMut].add i

    of nnkCall, nnkCommand, nnkInfix, nnkPrefix:
      if (let i = procMemberRefs.findIt(node, it[0]); i >= 0):
        result.add procMemberRefs[i][1]
      let mut = node[0].paramsMut
      for i, node in node[1..^1]:
        result.add getMemberRefs(node, mut[i])

    of nnkAsgn:
      if (let i = members.find(node[0]); i >= 0):
        result[refmMut].add i
      result.add getMemberRefs(node[1])

    of nnkBracketExpr, nnkDotExpr:
      result.add getMemberRefs(node[0], varCtx)
      for node in node[1..^1]: result.add getMemberRefs(node)

    of AtomicNodes - {nnkSym}: discard

    else:
      for node in node:
        result.add getMemberRefs(node, varCtx)

  proc memberValAccess(sym: NimNode): NimNode =
    assert sym.kind == nnkSym
    assert sym in members
    let ident = ident($sym)
    quote do: `ident`.val[]

  proc withMemberValAccess(node: NimNode): NimNode =
    proc impl(node: NimNode): NimNode =
      case node.kind
      of nnkSym:
        result =
          if node in members: node.memberValAccess
          else: node

      of complement(AtomicNodes):
        result = node.kind.newTree()
        for node in node:
          result.add impl(node)

      else: result = node

    impl(node.undoHiddenNodes)


  # ---- generate members and other init code ----

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
            let (sym, isExported) =
              if sym.kind == nnkPostfix:
                assert $sym[0] == "*"
                (sym[1], true)
              else:
                (sym, sym.isExported)
            let ident = ident($sym)

            if not (isExported or isVar):
              initSection.add: quote do:
                let `ident` = `defaultVal`
            else:
              members.add sym
              initSection.add: quote do:
                let `ident` = newPatchRef(`defaultVal`)
              if sym.isExported:
                pubMembers.add newColonExpr(ident, ident)

      of nnkProcDef, nnkFuncDef:
        procMemberRefs.add (node[0], getMemberRefs(node))
        initSection.add node.withMemberValAccess

      else:
        initSection.add node

  scanBody inputInitSection.undoHiddenNodes


  # ---- generate elements defenitions ----

  proc defElems(templ: Templ) =
    for elem in templ:
      let elemSym = elem.sym
      
      case elem.kind
      of templText:
        initSection.add: quote do:
          var `elemSym` = document.createTextNode("")
      
      of templTag:
        let tag = elem.tag
        initSection.add: quote do:
          var `elemSym` = document.createElement(`tag`)
        for event, action in elem.handlers:
          let refs = getMemberRefs(action)[refmMut]
          let action = action.withMemberValAccess
          var procBody = newStmtList(action)
          for i in refs:
            let member = ident($members[i])
            procBody.add: quote do:
              patch `member`
          initSection.add: quote do:
            `elemSym`.addEventListener(`event`) do (_: Event):
              `procBody`
        defElems elem.childs

      of templComponent:
        let component = elem.component
        initSection.add: quote do:
          var `elemSym` = `component`()

      of templFor:
        var initMembers = newStmtList()
        for forVar in elem.forHead.getForVars:
          let val = newCall(bindSym"default", newCall(bindSym"typeof", forVar))
          initMembers.add:
            if forVar.isVar: newVarStmt(forVar.postfix("*"), val)
            else:            newLetStmt(forVar.postfix("*"), val)

        let component = elem.forComponent
        let componentDef = componentImpl(initMembers, elem.forBody, members)
        initSection.add: quote do:
          let `component` = `componentDef`
          var `elemSym`: instanceSeqType(`component`)

  defElems templ


  # ---- build component instance fields ----
    
  let rootParent = genSym(nskVar, "parent")
  let rootGetHookProc = genSym(nskVar, "getHook")

  initSection.add: quote do:
    var `rootParent`: Node
    var `rootGetHookProc`: proc: Node

  proc getHookProc(hook: NimNode): NimNode =
    if hook != nil:
      quote do:
        when `hook` is Node:
          proc: Node = `hook`
        else: `hook`.getFirstNode
    else:
      rootGetHookProc


  let mountProc = block:
    var procBody = newStmtList()

    template addPatchProcAndInit(origCode: NimNode, action: untyped) =
      let memberRefs = getMemberRefs(origCode)[refmAll]
      let code {.inject.} = origCode.withMemberValAccess
      if len(memberRefs) == 0:
        procBody.add: quote do:
          action
      else:
        let patchProc {.inject.} = genSym(nskProc, "patch")
        procBody.add: quote do:
          proc `patchProc` {.closure.} =
            action
          `patchProc`()
        for i in memberRefs:
          let member {.inject.} = ident($members[i])
          procBody.add: quote do:
            `member`.patchProcs.procs.add newPatchProc(`patchProc`)

    proc buildProcBody(templ: Templ, parent: NimNode = nil) =
      var hookElemSym: NimNode
      for elem in templ.revItems:
        let elemSym = elem.sym

        proc mountPlainDomElem =
          let hook =
            if hookElemSym == nil:
              if parent == nil: newCall(rootGetHookProc)
              else: nil
            else:
              quote do: `hookElemSym`.getFirstNode()
          let parent =
            if parent == nil: rootParent
            else: parent
          procBody.add:
            if hook == nil:
              quote do:
                `parent`.appendChild(`elemSym`)
            else:
              quote do:
                `parent`.insertBefore(`elemSym`, `hook`)

        case elem.kind
        of templText:
          addPatchProcAndInit elem.text:
            `elemSym`.data = `code`
          mountPlainDomElem()

        of templTag:
          for attr, val in elem.attrs:
            addPatchProcAndInit val:
              `elemSym`.setAttrProperly(`attr`, `code`)
          mountPlainDomElem()
          buildProcBody(elem.childs, parent=elemSym)

        of templComponent:
          # init members
          for name, val in elem.params:
            let paramIdent = ident(name)
            if val in members:
              let val = val.unbindSyms
              procBody.add: quote do:
                `elemSym`.pubMembers.`paramIdent` = `val`
            else:
              let unboundVal = val.withMemberValAccess
              procBody.add: quote do:
                `elemSym`.pubMembers.`paramIdent`.val = 
                  when compiles(addr `unboundVal`):
                    cast[typeof(`elemSym`.pubMembers.`paramIdent`.val)](addr `unboundVal`)
                  else:
                    new `unboundVal`

              for i in val.getMemberRefs[refmAll]:
                let member = members[i].unbindSyms
                procBody.add: quote do:
                  `elemSym`.pubMembers.`paramIdent`.patchProcs.procs.add newPatchProcGroup(`member`.patchProcs)
                  `member`.patchProcs.procs.add newPatchProcGroup(`elemSym`.pubMembers.`paramIdent`.patchProcs)

          # mount
          let getHook = hookElemSym.getHookProc
          let parent =
            if parent == nil: rootParent
            else: parent
          procBody.add: quote do:
            `elemSym`.mount(`parent`, `getHook`)

        of templFor:
          let getHook = hookElemSym.getHookProc
          procBody.add: quote do:
            `elemSym`.getHook = `getHook`

        hookElemSym = elemSym

    buildProcBody(templ)
    quote do:
      proc (parent: Node, getHook: proc: Node) =
        `rootParent` = parent
        `rootGetHookProc` = getHook
        `procBody`


  let detachProc = block:
    var procBody = newStmtList()
    for elem in templ:
      let sym = elem.sym
      procBody.add:
        case elem.kind
        of templText, templTag:
          quote do:
            `rootParent`.removeChild(`sym`)

        of templComponent:
          quote do:
              `sym`.detach()

        of templFor:
          quote do:
            for elem in `sym`.instances:
              elem.detach()

    quote do:
      proc =
        `procBody`
        `rootParent` = nil


  # ---- assamble ----

  result = quote do:
    proc: auto =
      `initSection`
      result = newComponentInstance(`pubMembers`)
      result.mount = `mountProc`

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



proc run*(component: Component[tuple[]]) =
  component().mount(document.body, proc: Node = nil)