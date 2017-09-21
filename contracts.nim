import strutils, macros

const msgFmt = "implements: $#"

type
  ConceptIdEntry = tuple[sym, def: NimNode]
# TODO: find out why using ConceptIdEntry itself as the id makes the compiler
# quit without an error message (hint: static[]). Using a string rep instead
# should not be necessary.
  ConceptId = string
  ConceptIdTyClass[id: static[ConceptId]] = distinct auto

template flagProcDef(T: untyped, cId: ConceptId): untyped =
  proc explImpl(Ty: typedesc[T], Co: typedesc[ConceptIdTyClass[cId]]): bool = true

template flagProcQuery(T: untyped, cId: ConceptId): untyped =
  compiles explImpl(T, ConceptIdTyClass[cId])

proc resolveImpl(cid: ConceptIdEntry): ConceptIdEntry =
  var
    im = cid.def.symbol.getImpl
    spec = im[2]

  case spec.kind
  of nnkTypeClassTy:  # regular concept spec
    (cid.sym, im)
  of nnkSym:                  # type alias: use aliased concept symbol so that
    (spec, spec).resolveImpl  # aliased and alias concept have identical ids.
  of nnkDistinctTy:                 # distinct type: use its own symbol with
    (cid.sym, spec[0]).resolveImpl  # the original concept definition as id.
  else:
    error(msgFmt % "unexpected type specification " & $spec.kind, cid.sym)
    (nil, nil)

proc structuredId(n: NimNode): ConceptIdEntry =
  (n, n).resolveImpl

proc id(n: NimNode): ConceptId =
  var impl = n.structuredId
  impl.sym.treeRepr & " | " & impl.def.treeRepr

macro explicitlyImplements*(T, C: typed): untyped =
  getAst flagProcQuery(T, C.id)

macro addImpl(t, c: typed): NimNode =
# TODO: implement this:
#  if not compiles(var dummy = c.isAbsolutelyExplicitish):
#    warning msgFmt % $c.symbol & " is not explicit, statement regarding it " &
#      "is purely informational and will be ignored."
  #echo flagProcQuery(t, c.id)
  getAst flagProcDef(t, c.id)

proc expectKind(n: NimNode, k: NimNodeKind, msg: string) =
  if k != n.kind:
    error(msg, n)

proc expectConcept(n: NimNode, msg: string) =
  # TODO: how do we check this in an alias-proof way?
  #if n.getType[1].findChild(nnkSym == it.kind and "concept" == it.repr) != nil:
  #  error(msg, n)
  #var (_, def) = n.structuredId
  discard

proc rejectGeneric(n: NimNode, msg: string) =
  # TODO: use resolveImpl
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
  echo result[^1].treeRepr
