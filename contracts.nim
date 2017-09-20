import strutils, macros

const msgFmt = "implements: $#"

macro dumpTreeTyped*(b: typed): untyped =
  result = newStmtList()
  echo treeRepr(b)

macro displayTree*(b: untyped): untyped =
  result = b
  echo treeRepr(b)

type
#  ConceptIdEntry = tuple[idt, def: NimNode]
#  ConceptId = object
#    entry: ConceptIdEntry
#    refined: openArray[ConceptIdEntry]
  ConceptId = string
  ConceptIdTyClass[id: static[ConceptId]] = distinct auto

template flagProcDef(T: untyped, cId: ConceptId): untyped =
  proc explImpl(Ty: typedesc[T], Co: typedesc[ConceptIdTyClass[cId]]): bool = true

template flagProcQuery(T: untyped, cId: ConceptId): untyped =
  compiles explImpl(T, ConceptIdTyClass[cId])

proc id(n: NimNode): ConceptId =
  n.symbol.getImpl.treeRepr
#  echo C.symbol.getImpl.treeRepr
#  echo C.symbol.getImpl[2][2][0].symbol.getImpl.repr
#  echo C.symbol.getImpl[2].symbol.getImpl.repr

macro explicitlyImplements*(T, C: typed): untyped =
  getAst flagProcQuery(T, C.id)

macro addImpl(t, c: untyped): NimNode =
#  if not compiles(var dummy = c.isAbsolutelyExplicitish):
#    warning msgFmt % $c.symbol & " is not explicit, statement regarding it " &
#      "is purely informational and will be ignored."
  getAst flagProcDef(t, c.id)

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
      result.add getAst addImpl(im, c)
