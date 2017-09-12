import contracts, macros
import sets as willy

type
  C = concept c
    c.n is int

  D[T] = concept d
    d.x is T

  Di = distinct D[int]

  X = object
    n: int

  Y[T] = object
    x: T

macro show(b: typed): untyped =
  result = newStmtList()
  echo treeRepr(b)

implements C: int
implements C, Di: X
implements Di:
  type
    A = float

echo X.explicitlyImplements C
echo X.explicitlyImplements Di
echo int.explicitlyImplements C
echo int.explicitlyImplements Di
echo A.explicitlyImplements Di
