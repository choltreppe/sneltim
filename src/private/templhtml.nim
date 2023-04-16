#
#    Sneltim - A svelte-like web-frontend framework for nim
#        (c) Copyright 2023 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, genasts, typetraits, sugar, strformat, strutils, sequtils, setutils, tables, options]
import fusion/matching
import ./utils


type
  MemberKind* = enum priv, pubLet, pubVar

  CodeBlockId* = distinct int
  CodeBlock* = object
    code*, codeRaw*: NimNode
    refs*: array[MemberKind, seq[int]]
    isStmt*: bool

  TemplElemKind* = enum templText, templTag, templComponent, templFor#, templIf
  TemplElem* = ref object
    sym*: NimNode

    case kind*: TemplElemKind
    of templText:
      text*: CodeBlockId

    of templTag:
      tag*: string
      attrs*: Table[string, CodeBlockId]
      handlers*: Table[string, CodeBlockId]

    of templComponent:
      component*: CodeBlockId
      pubMembers*: array[pubLet..pubVar, seq[string]]
      vars*: Table[string, CodeBlockId]

    of templFor:
      forHead*: CodeBlockId
      forBody*: Templ
      forComponent*: NimNode

    parentId*: int
    hookId*: int = -1

  Templ* = object
    elems*: seq[TemplElem]
    codeBlocks*: seq[CodeBlock]


func toAstGen(id: CodeBlockId): NimNode =
  newCall(bindSym"CodeBlockId", newLit(id.distinctBase))

func toAstGen(table: Table[string, CodeBlockId]): NimNode =
  var tableConstr = nnkTableConstr.newTree()
  for k, v in table:
    tableConstr.add nnkExprColonExpr.newTree(newLit(k), v.toAstGen)
  quote do:
    toTable[string, CodeBlockId](`tableConstr`)

func toAstGen*(templ: Templ): NimNode

func toAstGen(elem: TemplElem): NimNode =
  result = nnkObjConstr.newTree(bindSym"TemplElem")
  template addField(name: string, val: NimNode) =
    result.add nnkExprColonExpr.newTree(ident(name), val)
  addField("kind", newLit(elem.kind))
  addField("parentId", newLit(elem.parentId))
  addField("hookId", newLit(elem.hookId))
  case elem.kind
  of templText:
    addField("text", elem.text.toAstGen)
  of templTag:
    addField("tag", newLit(elem.tag))
    addField("attrs", elem.attrs.toAstGen)
    addField("handlers", elem.handlers.toAstGen)
  of templComponent:
    addField("component", elem.component.toAstGen)
    addField("pubMembers"): genAst(m = elem.pubMembers):
      m
    addField("vars", elem.vars.toAstGen)
  of templFor:
    addField("forHead", elem.forHead.toAstGen)
    addField("forBody", elem.forBody.toAstGen)

func toAstGen*(templ: Templ): NimNode =
  var elems = nnkBracket.newTree()
  for elem in templ.elems:
    elems.add elem.toAstGen
  quote do:
    Templ(elems: @`elems`)


proc parseTempl*(body: NimNode): Templ =

  var templ: Templ

  proc setCodeBlock(field: var CodeBlockId, code: NimNode, isStmt = false) =
    templ.codeBlocks &= CodeBlock(code: code, isStmt: isStmt)
    field = CodeBlockId(high(templ.codeBlocks))

  proc setCodeBlock(table: var Table[string, CodeBlockId], key: string, code: NimNode, isStmt = false) =
    table.mgetOrPut(key, CodeBlockId(0)).setCodeBlock(code, isStmt)


  proc parseElem(node: NimNode, parentId = -1): int =
    templ.elems &= TemplElem(parentId: parentId)
    result = high(templ.elems)

    proc elemParts: tuple[
      ident: NimNode,
      params: seq[tuple[pre,name: string, val: NimNode]],
      body: NimNode
    ] =
      let head =
        case len(node)
        of 2:
          if node[1].kind == nnkCommand:
            node[1].expectLen 2  #TODO: err msg
            result.body = node[1][1]
            node[1][0]
          else:
            result.body = newEmptyNode()
            node[1]
        of 3:
          result.body = node[2]
          node[1]
        else:
          assert false  #TODO: err msg
          quit 1

      template setIdent(nodeExpr: NimNode) =
        let node =
          if nodeExpr.kind == nnkAccQuoted: nodeExpr[0]
          else: nodeExpr
        node.expectKind {nnkIdent, nnkSym}  #TODO: err msg
        result.ident = node

      if head.kind == nnkCall:
        setIdent head[0]
        for node in head[1..^1]:
          node.expectKind nnkExprEqExpr  #TODO: err msg
          result.params.add:
            if node[0].kind == nnkDotExpr:
              node[0][0].expectKind nnkIdent  #TODO: err msg
              node[0][1].expectKind nnkIdent  #TODO: err msg
              (node[0][0].strVal, node[0][1].strVal, node[1])
            else:
              node[0].expectKind nnkIdent
              ("", node[0].strVal, node[1])
      else:
        setIdent head

    proc parseChilds(body: NimNode, parentId: int) =
      if body.kind != nnkEmpty:
        var prevId = -1
        for node in body.denestStmtList:
          let id = parseElem(node, parentId)
          if prevId >= 0:
            templ.elems[prevId].hookId = id
          prevId = id

    if node.kind == nnkPrefix and node[0].strVal == "<":
      let (ident, params, body) = elemParts()
      templ.elems[^1].kind = templTag
      templ.elems[^1].tag = ident.strVal
      for (pre, name, val) in params:
        case pre
        of "": templ.elems[^1].attrs.setCodeBlock(name, val)
        of "on": templ.elems[^1].handlers.setCodeBlock(name, val, isStmt=true)
        else: assert false  #TODO: err msg
      parseChilds(body, result)
    
    elif node.kind == nnkPrefix and node[0].strVal == "<%":
      let (ident, params, body) = elemParts()
      templ.elems[^1].kind = templComponent
      templ.elems[^1].component.setCodeBlock(ident)
      for (pre, name, val) in params:
        assert pre == ""  #TODO: err msg
        templ.elems[^1].vars.setCodeBlock(name, val)
      parseChilds(body, result)

    elif node.kind == nnkForStmt:
      templ.elems[^1].kind = templFor
      var forHead = nnkForStmt.newTree()
      for node in node[0 ..< ^1]:
        forHead.add node
      forHead.add newEmptyNode()
      templ.elems[^1].forHead.setCodeBlock(forHead, isStmt=true)
      templ.elems[^1].forBody = parseTempl(node[^1])

    else:
      debugEcho treerepr node
      templ.elems[^1].kind = templText
      templ.elems[^1].text.setCodeBlock(node)

  for node in body.denestStmtList:
    discard parseElem(node)

  templ