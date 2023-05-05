import std/[macros, genasts, sugar, sequtils, strutils, strformat, sets, tables]


type
  Op = enum opAdd="+", opSub="-"
  SizeKind = enum px, em, pct, vw, vh, vmin, vmax, calc
  Size* = ref object
    case kind: SizeKind
    of calc:
      op: Op
      lhs,rhs: Size
    else:
      case isFloat: bool
      of true:  fval: float
      of false: ival: int

func `$`*(s: Size): string =
  func showCalc(s: Size): string =
    if s.kind == calc:
      "(" & showCalc(s.lhs) & " " & $s.op & " " & showCalc(s.rhs) & ")"
    else: $s
  if s.kind == calc: "calc" & showCalc(s)
  else:
    ( if s.isFloat: $s.fval
      else:         $s.ival
    ) &
    ( if s.kind == pct: "%"
      else: $s.kind )

macro makeSizeInitFuncs: untyped =
  result = newStmtList()
  for k in px ..< calc:
    result.add genAst(k, v = ident"v", funcName = ident($k)) do:
      func funcName*(v: int|float): Size =
        when v is float: Size(kind: k, isFloat: true,  fval: v)
        else:            Size(kind: k, isFloat: false, ival: v)
makeSizeInitFuncs()


macro genSizeMulDiv: untyped =
  result = newStmtList()
  for op in ["*", "/"]:
    let opSym = nnkAccQuoted.newTree(ident(op))
    let ftype =
      if op == "*": genAst(float)
      else:         genAst(int|float)

    result.add genAst(opSym, s = ident"s", f = ident"f", ftype) do:
      func opSym*(s: Size, f: ftype): Size =
        if s.kind == calc:
          Size(kind: calc, op: s.op, lhs: opSym(s.lhs, f), rhs: opSym(s.rhs,f))
        else:
          Size(
            kind: s.kind,
            isFloat: true,
            fval: opSym( 
                    if s.isFloat: s.fval
                    else:   float(s.ival),
                    float(f)
                  )
          )

      template opSym*(f: int|float, s: Size): Size = opSym(s, f)

genSizeMulDiv()

func `*`*(s: Size, f: int): Size =
  if s.kind == calc:
    Size(kind: calc, op: s.op, lhs: s.lhs*f, rhs: s.rhs*f)
  else:
    if s.isFloat:
      Size(
        kind: s.kind,
        isFloat: true,
        fval: s.fval * float(f)
      )
    else:
      Size(
        kind: s.kind,
        isFloat: false,
        ival: s.ival * f
      )


macro genSizeAddSub =
  result = newStmtList()
  for opEnum in [opAdd, opSub]:
    let opSym = nnkAccQuoted.newTree(ident($opEnum))
    result.add genAst(opSym, opEnum, a = ident"a", b = ident"b") do:

      proc opSym*(a,b: Size): Size =
        if a.kind == b.kind and a.kind != calc:
          if not(a.isFloat) and not(b.isFloat):
            Size(
              kind: a.kind,
              isFloat: false,
              ival: opSym(a.ival, b.ival)
            )
          else:
            Size(
              kind: a.kind,
              isFloat: true,
              fval:
                if   not a.isFloat: opSym(float(a.ival),       b.fval )
                elif not b.isFloat: opSym(      a.fval , float(b.ival))
                else:               opSym(      a.fval ,       b.fval )
            )
        else:
          Size(kind: calc, op: opEnum, lhs: a, rhs: b)

genSizeAddSub()

template `-`*(s: Size): Size = s * -1