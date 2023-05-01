#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, genasts, typetraits, sequtils, strutils, setutils, sets, tables, dom, options, enumerate]
import fusion/matching
export dom

import sneltim/private/[templ, utils]
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
    skipPatchProcs: seq[proc()]

func new[T](v: T): ref T =
  new result
  result[] = v

func newPatchRef[T](val: T): PatchRef[T] =
  new result
  result.val = new val
  new result.patchProcs
  
proc add(pps: var PatchProcs, p: proc()) =
  pps.procs.add PatchProcsNode(isGroup: false, patchProc: p)

proc add(pps: var PatchProcs, g: PatchProcs) =
  pps.procs.add PatchProcsNode(isGroup: true, group: g)

proc connect(a,b: var PatchProcs) =
  a.add b
  b.add a

proc patch(pps: PatchProcs, skip: seq[proc()], visited = newSeq[PatchProcs]()) =
  if pps notin visited:
    var i = 0
    while i < len(pps.procs):
      let pp = pps.procs[i]
      if pp.isGroup:
        patch pp.group, skip, visited & pps
      else:
        if pp.patchProc notin skip:
          pp.patchProc()
      inc i

proc patch(pr: PatchRef, init = false) =
  if pr.val[] != pr.prevVal or init:
    pr.prevVal = pr.val[]
    patch pr.patchProcs, pr.skipPatchProcs


type
  Members = concept ms
    ms is tuple
    for m in ms.fields:
      m is PatchRef

  Slots = concept ss
    ss is tuple
    for s in ss.fields:
      s is BaseComponent

  ComponentInstance[M: Members, S: Slots] = object
    mount: proc(parent: Node, getHook: proc: Node)
    detach: proc()
    pubMembers: M
    slots: ref S
    getFirstNode: proc: Node

  ComponentInstanceSeq[M: Members, S: Slots] = object
    instances: seq[ComponentInstance[M,S]]
    getHook: proc: Node

  ComponentTuple = concept cs
    cs is tuple
    for c in cs.fields:
      c is ComponentInstance

  # sadly I didnt find a way to assert the len of the tuple on type-level, concepts seem to not accept generics (?)
  ComponentInstanceOptions[T: ComponentTuple] = object
    options: T
    active: int = -1

  Component[M: Members, S: Slots] = proc: ComponentInstance[M,S]

  BaseComponent = Component[tuple[], tuple[]]
  BaseComponentInstance = ComponentInstance[tuple[], tuple[]]

template    instanceType[M,S](c: Component[M,S]): type =    ComponentInstance[M,S]
template instanceSeqType[M,S](c: Component[M,S]): type = ComponentInstanceSeq[M,S]

func emptyComponent: BaseComponentInstance =
  var getHook: proc: Node = nil
  result.mount = proc(_: Node, h: proc: Node) =
    getHook = h
  result.detach = proc = discard
  result.getFirstNode = getHook

func newComponentInstance[M: Members, S: Slots](pubMembers: M, slots: ref S): ComponentInstance[M,S] =
  result.pubMembers = pubMembers
  result.slots = slots

proc newComponentInstanceOptions[T: ComponentTuple](options: T): ComponentInstanceOptions[T] =
  result.options = options
  result.active = -1

proc setActive*(
  options: var ComponentInstanceOptions,
  i: static int,
  parent: Node,
  getHook: proc: Node
) =
  if options.active != i:
    block detachPrevBranch:
      for j, o in enumerate(options.options.fields):
        if j == options.active:
          o.detach()
          break detachPrevBranch
    options.options[i].mount(parent, getHook)
    options.active = i

proc patch(c: ComponentInstance) =
  for member in c.pubMembers.fields:
    patch member

let namelessSlotField {.compiletime.} = genSym(nskField, "namelessSlot")
proc slotFieldName(name: string): NimNode =
  if name == "_": namelessSlotField
  else: ident(name)


func getFirstNode*(node: Node): Node {.inline.} = node

proc getFirstNode*(s: ComponentInstanceSeq): Node =
  if len(s.instances) > 0:
    s.instances[0].getFirstNode()
  else:
    s.getHook()

proc getFirstNode*(options: ComponentInstanceOptions): Node =
  for i, o in enumerate(options.options.fields):
    if i == options.active:
      return o.getFirstNode()


proc setAttrProperly*(node: Node, attr: string, val: auto) =
  let val = cstring($val)
  case attr
  of "value": node.value = val
  else: node.setAttr(attr, val)

proc patchBoundValue[T](bound: var T, node: Node) =
  let str = $node.value
  try:
    bound =
      when bound is cstring: node.value
      elif bound is string: str
      elif bound is int: parseInt(str)
      elif bound is SomeInteger: parseBiggestInt(str).typeof(bound)
      elif bound is float: parseFloat(str)
      elif bound is SomeFloat: parseBiggestInt(str).typeof(bound)
      else:
        static: error "invalid type for binding"
        return
  except ValueError:
    node.value = cstring($bound)


proc componentImpl(
  inputInitSection: NimNode,
  templ: Templ,
  inheritMembers = newSeq[NimNode](),
  inheritSlots = none(tuple[sym: NimNode, names: HashSet[string]])
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

      of AtomicNodes - {nnkSym}: result = node

      of nnkConv:
        result = nnkCall.newTree()
        for node in node:
          result.add impl(node)

      else:
        result = node.kind.newTree()
        for node in node:
          result.add impl(node)

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
              if isExported:
                pubMembers.add newColonExpr(ident, ident)

      of nnkProcDef, nnkFuncDef:
        procMemberRefs.add (node[0], getMemberRefs(node))
        initSection.add node.withMemberValAccess

      else:
        initSection.add node

  scanBody inputInitSection.undoHiddenNodes


  # ---- find slots in template ----

  let (slots, slotNames) = block:
    if Some(@info) ?= inheritSlots: info
    else:
      var slotNames: HashSet[string]
      proc getSlotNames(templ: Templ) =
        for elem in templ:
          case elem.kind
          of templSlot: slotNames.incl elem.slotName
          of templTag: getSlotNames elem.childs
          of templComponent:
            for body in elem.slots.values: getSlotNames body
          of templFor: getSlotNames elem.forBody
          of templIfCase:
            if elem.isCaseStmt:
              for (_, body) in elem.ofBranches: getSlotNames body
            for (_, _, body) in elem.elifBranches: getSlotNames body
            if Some(@body) ?= elem.elseBody: getSlotNames body
          of templText: discard
      getSlotNames templ

      let slots = genSym(nskLet, "slots")
      var slotsType = nnkTupleTy.newTree()
      for name in slotNames:
        let fieldName = slotFieldName(name)
        slotsType.add nnkIdentDefs.newTree(
          fieldName,
          bindSym"BaseComponent",
          newEmptyNode()
        )
      initSection.add: quote do:
        let `slots` = new default(`slotsType`)

      (slots, slotNames)


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

        proc addEventPatching(event: string, refs: seq[int], action: NimNode) =
          let action = action.withMemberValAccess
          var procBody = newStmtList(action)
          for i in refs:
            let member = ident($members[i])
            procBody.add: quote do:
              patch `member`
          initSection.add: quote do:
            `elemSym`.addEventListener(`event`) do (_: Event):
              `procBody`

        for event, action in elem.handlers:
          addEventPatching(event, getMemberRefs(action)[refmMut], action)

        for name, (val, bound) in elem.attrs:
          if bound:
            case name
            of "value":
              addEventPatching("input", getMemberRefs(val, varCtx=true)[refmMut]): quote do:
                patchBoundValue(`val`, `elemSym`)
            else:
              error "cant bind "&name, val

        defElems elem.childs

      of templComponent:
        let component = elem.component
        initSection.add: quote do:
          var `elemSym` = `component`()
        for name, body in elem.slots:
          let fieldName = slotFieldName(name)
          let slotComponent = componentImpl(newStmtList(), body, members, some((slots, slotNames)))
          initSection.add: quote do:
            `elemSym`.slots[].`fieldName` = `slotComponent`

      of templSlot:
        initSection.add: quote do:
          var `elemSym`: BaseComponentInstance

      of templFor:
        var initMembers = newStmtList()
        for forVar in elem.forHead.getForVars:
          let val = newCall(bindSym"default", newCall(bindSym"typeof", forVar))
          initMembers.add:
            if forVar.isVar: newVarStmt(forVar.postfix("*"), val)
            else:            newLetStmt(forVar.postfix("*"), val)

        let component = elem.forComponent
        let componentDef = componentImpl(initMembers, elem.forBody, members, some((slots, slotNames)))
        initSection.add: quote do:
          let `component` = `componentDef`
          var `elemSym`: instanceSeqType(`component`)

      of templIfCase:
        var options = nnkTupleConstr.newTree()
        proc addOptionComponent(body: Templ, defs = newSeq[NimNode]()) =
          var initMembers = newStmtList()
          for sym in defs:
            let val = newCall(bindSym"default", newCall(bindSym"typeof", sym))
            initMembers.add newLetStmt(sym.postfix("*"), val)
          let component = genSym(nskLet, "branchComponent")
          let componentDef = componentImpl(initMembers, body, members, some((slots, slotNames)))
          initSection.add: quote do:
            let `component` = `componentDef`
          options.add newCall(component)

        if elem.isCaseStmt:
          for (_, body) in elem.ofBranches:
            addOptionComponent body

        for (_, defs, body) in elem.elifBranches:
          addOptionComponent body, defs

        if Some(@body) ?= elem.elseBody:
          addOptionComponent body
        else:
          options.add newCall(bindSym"emptyComponent")

        initSection.add: quote do:
          var `elemSym` = newComponentInstanceOptions(`options`)

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
        when `hook` is ComponentInstance:
          `hook`.getFirstNode
        else:
          proc: Node = getFirstNode(`hook`)
    else:
      rootGetHookProc


  let mountProc = block:
    var procBody = newStmtList()

    proc addPatchProcAndInit(origCode: NimNode, action: proc(code: NimNode): NimNode) =
      let memberRefs = getMemberRefs(origCode)[refmAll]
      let code = origCode.withMemberValAccess
      let action = action(code)
      if len(memberRefs) == 0:
        initSection.add action
      else:
        let patchProc = genSym(nskProc, "patch")
        procBody.add: quote do:
          proc `patchProc` {.closure.} =
            `action`
          `patchProc`()
        for i in memberRefs:
          let member = ident($members[i])
          procBody.add: quote do:
            `member`.patchProcs.add `patchProc`

    proc buildInstanceMemberInit(instance, member, val: NimNode, useType=false): NimNode =
      result = newStmtList()
      if val in members:
        let val = val.unbindSyms
        result.add: quote do:
          `instance`.pubMembers.`member`[] = `val`[]
      else:
        let unboundVal = val.withMemberValAccess
        let isVar = not useType or val.isVar
        result.add: quote do:
          `instance`.pubMembers.`member`.val = 
            when `isVar` and compiles(addr `unboundVal`):
              cast[typeof(`instance`.pubMembers.`member`.val)](addr `unboundVal`)
            else:
              new `unboundVal`

    proc buildProcBody(templ: Templ, parent: NimNode = nil) =
      var hookElemSym: NimNode

      for elem in templ.revItems:
        let elemSym = elem.sym

        let (hook, getHook) =
          if hookElemSym == nil:
            if parent == nil: (newCall(rootGetHookProc), rootGetHookProc)
            else: (
              newNilLit(),
              quote do:
                proc: Node = nil
            )
          else: (
            (quote do: `hookElemSym`.getFirstNode()),
            quote do:
              when `hookElemSym` is ComponentInstance:
                `hookElemSym`.getFirstNode
              else:
                proc: Node = getFirstNode(`hookElemSym`)
          )
        let parent =
          if parent == nil: rootParent
          else: parent

        proc mountPlainDomElem =
          procBody.add: quote do:
            let hook: Node = `hook`
            if hook == nil:
              `parent`.appendChild(`elemSym`)
            else:
              `parent`.insertBefore(`elemSym`, hook)

        case elem.kind
        of templText:
          addPatchProcAndInit(elem.text) do(code: NimNode) -> NimNode: quote do:
            `elemSym`.data = cstring($`code`)
          mountPlainDomElem()

        of templTag:
          for attr, (val, _) in elem.attrs:
            addPatchProcAndInit(val) do(code: NimNode) -> NimNode: quote do:
              `elemSym`.setAttrProperly(`attr`, `code`)
          mountPlainDomElem()
          buildProcBody(elem.childs, parent=elemSym)

        of templComponent:
          for name, val in elem.params:
            let member = ident(name)
            procBody.add buildInstanceMemberInit(elemSym, member, val)
            for i in val.getMemberRefs[refmAll]:
              let ownMember = members[i].unbindSyms
              procBody.add: quote do:
                connect `elemSym`.pubMembers.`member`.patchProcs, `ownMember`.patchProcs

          procBody.add: quote do:
            `elemSym`.mount(`parent`, `getHook`)

        of templSlot:
          let fieldName = slotFieldName(elem.slotName)
          procBody.add: quote do:
            `elemSym` = `slots`[].`fieldName`()
            `elemSym`.mount(`parent`, `getHook`)

        of templFor:
          procBody.add: quote do:
            `elemSym`.getHook = `getHook`

          let patchProc = genSym(nskProc, "patch")
          procBody.add: quote do:
            proc `patchProc` {.closure.}

          var patchBody = newStmtList()
          let component = elem.forComponent

          let instanceId = genSym(nskVar, "i")
          patchBody.add: quote do:
            var `instanceId` = 0

          var forStmt = elem.forHead.withMemberValAccess
          var updateLetForMembers = newStmtList()
          var mountNewInstance = newStmtList: quote do:
            `elemSym`.instances.add `component`()
          let instance = quote do:
            `elemSym`.instances[`instanceId`]

          for forVar in elem.forHead.getForVars:
            let member = forVar.unbindSyms
            mountNewInstance.add buildInstanceMemberInit(
              instance, member, forVar, useType=true)
            for i in elem.forHead.getMemberRefs[refmAll]:
              let ownMember = members[i].unbindSyms
              mountNewInstance.add: quote do:
                `instance`.pubMembers.`member`.patchProcs.add `ownMember`.patchProcs
            mountNewInstance.add: quote do:
              `instance`.pubMembers.`member`.skipPatchProcs.add `patchProc`
            if not forVar.isVar:
              updateLetForMembers.add: quote do:
                `instance`.pubMembers.`member`.val[] = `member`

          for i in elem.forHead.getMemberRefs[refmAll]:
            let member = members[i].unbindSyms
            mountNewInstance.add: quote do:
              `member`.patchProcs.add `patchProc`
              
          mountNewInstance.add: quote do:
            `instance`.mount(`parent`, `elemSym`.getHook)
          forStmt[^1] = quote do:
            if `instanceId` < len(`elemSym`.instances):
              `updateLetForMembers`
              patch `instance`
            else:
              `mountNewInstance`
            inc `instanceId`
          patchBody.add forStmt

          patchBody.add: quote do:
            if `instanceId` < len(`elemSym`.instances):
              for i in `instanceId` ..< len(`elemSym`.instances):
                `elemSym`.instances[i].detach()
              `elemSym`.instances.setLen `instanceId`

          procBody.add: quote do:
            proc `patchProc` {.closure.} = `patchBody`
            `patchProc`()

        of templIfCase:
          var patchBody =
            if elem.isCaseStmt: nnkCaseStmt.newTree(elem.caseHead.withMemberValAccess)
            else: nnkIfStmt.newTree()

          var i = 0

          if elem.isCaseStmt:
            for (matches, _) in elem.ofBranches:
              var branch = nnkOfBranch.newTree()
              for match in matches:
                branch.add match.unbindSyms
              branch.add: quote do:
                `elemSym`.setActive(`i`, `parent`, `getHook`)
              patchBody.add branch
              inc i

          for (cond, defs, _) in elem.elifBranches:
            var updateMembers = newStmtList()
            for sym in defs:
              let member = sym.unbindSyms
              updateMembers.add: quote do:
                `elemSym`.options[`i`].pubMembers.`member`.val[] = `member`
                patch `elemSym`.options[`i`].pubMembers.`member`

            patchBody.add nnkElifBranch.newTree(
              cond.withMemberValAccess,
              newStmtList(
                updateMembers,
                quote do:
                  `elemSym`.setActive(`i`, `parent`, `getHook`)
              )
            )
            inc i

          patchBody.add: nnkElse.newTree: quote do:
                `elemSym`.setActive(`i`, `parent`, `getHook`)

          let patchProc = genSym(nskProc, "patch")
          procBody.add: quote do:
            proc `patchProc` {.closure.} =
              debugEcho "patch if/case"
              `patchBody`

          var refs: seq[int]
          if elem.isCaseStmt:
            refs.add getMemberRefs(elem.caseHead)[refmAll]
          for (cond, _, _) in elem.elifBranches:
            refs.add getMemberRefs(cond)[refmAll]
          refs = deduplicate(refs)
          for i in refs:
            let member = members[i].unbindSyms
            procBody.add: quote do:
              `member`.patchProcs.add `patchProc`

          procBody.add: quote do:
            `patchProc`()

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
      let elemSym = elem.sym
      procBody.add:
        case elem.kind
        of templText, templTag:
          quote do:
            `rootParent`.removeChild(`elemSym`)

        of templComponent, templSlot:
          quote do:
            `elemSym`.detach()

        of templFor:
          quote do:
            for elem in `elemSym`.instances:
              elem.detach()

        of templIfCase:
          quote do:
            for i, o in enumerate(`elemSym`.options.fields):
              if `elemSym`.active == i:
                o.detach()

    quote do:
      proc =
        `procBody`
        `rootParent` = nil


  let getFirstNodeProc = block:
    let firstNode = templ[0].sym
    quote do:
      proc: Node = `firstNode`.getFirstNode()


  # ---- assamble ----

  result = quote do:
    proc: auto =
      `initSection`
      result = newComponentInstance(`pubMembers`, `slots`)
      result.mount = `mountProc`
      result.detach = `detachProc`
      result.getFirstNode = `getFirstNodeProc`

  #debugEcho result.repr



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
  #debugEcho templ

  componentImpl(initSection, templ)



proc run*(component: BaseComponent) =
  component().mount(document.body, proc: Node = nil)