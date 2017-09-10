import strutils, macros, typetraits, hashes, sets, tables

const errMsgFmt = "implements $#: "


# ------------------ Helpers

# Should this be in the sets module?
proc newSet[A](initialSize = 64): ref HashSet[A] =
  result = new HashSet[A]
  result[].init initialSize

type
  # Is the name really the best type id we have? A TypeInfo object would be
  # nice, a "concrete typedesc with an address".
  TypeId = NimNode

template typeId(t: typedesc): TypeId =
  # Note: passing a concept's typedesc as a proc parameter explodes the
  # compiler, so this is also useful for converting them in call-site.
  name(t)

template typeId(t: NimNode): TypeId =
  #repr t.getType
  t

template typeId(t: auto): TypeId =
  typeId(type(t))

# Key: concept, value: implementations
# Is there a type class for concepts?
var impls = initTable[TypeId, ref HashSet[TypeId]](16)

# States that a given type implements a concept.
proc addImpl(t, c: TypeId) =
  var entry = impls.mgetOrPut(c, newSet[TypeId](16))
  entry[].incl t

# Checks whether a given type implements a concept.
proc queryImpl(t, c: TypeId): bool =
  var entry = impls.getOrDefault(c)
  if (entry == nil):
    false
  else:
    entry[].contains t

type
  # A contract checks the explicit implementation relation at compile time
  Contract[T] = concept type C
    explicitlyImplements(T, C)

template singleImpl(t, c: untyped) =
  addImpl(typeId t, typeId c)

template explicitlyImplements(t, c: typed): bool =
  queryImpl(typeId t, typeId c)

template implementsChecked(t, c: typed): bool =
  explicitlyImplements(t, c) and c is Contract

template implementsUnchecked(t, c: typed): bool =
  explicitlyImplements(t, c) and not implementsChecked(t, c)

iterator concepts(n: NimNode): NimNode =
  for c in n:
    if nnkStmtList == c.kind: break
    if not (c.kind in [nnkSym, nnkBracketExpr]):
      error(errMsgFmt % ["syntax error"], n)
    yield c

iterator implementations(n: NimNode): NimNode =
  for t in n:
    var i =
      if nnkTypeSection == n.kind: t[0]
      else: t
    if not (nnkSym == i.kind):
      error(errMsgFmt % ["syntax error"], n)
    yield i


proc typeSigs(n: NimNode): string =
  "$# | $#" % [repr n.getTypeInst, repr n.getTypeImpl]

macro implements(args: varargs[typed]): typed =
  result = newStmtList()
  echo treeRepr(args)
  args.expectKind(nnkBracket)
  var stmts = args.findChild(nnkStmtList == it.kind)
  if isNil(stmts):
    error(errMsgFmt % "expects an implementing type", args)
  if nnkTypeSection == stmts[0].kind:
    result.add stmts[0]
    stmts = stmts[0]
  for c in args.concepts:
    #echo "c: ", c.typeSigs
#    echo treeRepr c.getType
    for i in stmts.implementations:
#      echo i.sameType(c)
      #echo "i: ", i.typeSigs
      singleImpl(i, c)

type
  C = concept c
    c.n is int

  D[T] = concept d
    d.x is T

  X = object
    n: int

  Y[T] = object
    x: T

#singleImpl(X, C)
#singleImpl(Y, D)
#singleImpl(X, D)

implements C, D[float]:
  type
    Z = distinct int
#    A = float
#implements D: Y

#[
dumpTree:
Keeper implements MyContract, MyContract2

macro contract(name: untyped, rest: varargs[untyped]): untyped =
  result = newStmtList()
  echo repr(result)

dumpTree:
  contract MyContract c, ref d:
    type(c) is type( d)

dumpTree:
  type MyContract = concept c, ref d
    type(c) is type(d)

proc print(c: MyContract) =
  echo "is one"

let k = X(n: 3)
let l = Y[float](x: 3)
echo explicitlyImplements(k, C)
echo explicitlyImplements(X, C)
echo explicitlyImplements(Y, C)
echo explicitlyImplements(string, C)
]#
