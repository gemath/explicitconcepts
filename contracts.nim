import strutils, macros

const msgFmt = "implements: $#"

type
  # TODO: How do we mark Contracts?
  # A contract checks the explicit implementation relation at compile time.
  Contract = concept c
    const isAbsolutelyContractish = true
    #explicitlyImplements(T, C)

proc explicitlyImplements*(t: typedesc, c: typedesc): bool = false

template addProc(t, c: untyped): NimNode =
  proc explicitlyImplements*(ty: typedesc[t], co: typedesc[c]): bool = true

macro addImpl(t, c: typed): NimNode =
#  if not compiles(var dummy = c.isAbsolutelyContractish):
#    warning msgFmt % $c.symbol & " is not a Contract, statement regarding it " &
#      "is informational and will not be checked"
  getAst addProc(t, c)

proc expectKind(n: NimNode, k: NimNodeKind, msg: string) =
  if k != n.kind:
    error(msg, n)

proc expectConcept(n: NimNode, msg: string) =
  # TODO: how do we check this in an alias-proof way?
  #if n.getType[1].findChild(nnkSym == it.kind and "concept" == it.repr) != nil:
  #  error(msg, n)
  discard

proc rejectGeneric(n: NimNode, msg: string) =
  if n.symbol.getImpl.findChild(it.kind == nnkGenericParams) != nil:
    error(msg, n)

macro implements*(args: varargs[typed]): typed =
  result = newStmtList()
  args.expectKind(nnkBracket)
  var stmts = args.findChild(it.kind in {nnkStmtList, nnkStmtListExpr})
  if isNil(stmts):
    error(msgFmt % "expects an implementing type", args)
  if nnkTypeSection == stmts[0].kind:
    stmts = stmts[0]
    result.add stmts
  for c in args:
    if c.kind in {nnkStmtList, nnkStmtListExpr}:
      break
    expectKind(c, nnkSym, msgFmt % "syntax error in concepts list")
    expectConcept(c, msgFmt % "not a concept")
    rejectGeneric(c, msgFmt % "generic instantiations are not allowed")
    for i in stmts:
      var im = if nnkTypeDef == i.kind: i[0] else: i
      expectKind(im, nnkSym, msgFmt % "syntax error in implementations spec")
      result.add getAst(addImpl(im, c))
#[
macro contract(name: untyped, rest: varargs[untyped]): untyped =
  result = newStmtList()
  echo repr(result)

dumpTree:
  contract MyContract c, ref d:
    type(c) is type( d)

dumpTree:
  type MyContract = concept c, ref d
    type(c) is type(d)
]#
