import contracts, macros

macro show(b: typed): untyped =
  result = newStmtList()
  echo treeRepr(b)

type
  Co = concept c
    c.n is int

  D[T] = concept d
    d.v is T

  Di = distinct D[int]

  X = object
    n: int

  W = object
    v: float

  Y[T] = object
    v: T

#type CCoChecked = explicit Co
#type CCoChecked = ContractMarker[Co]

type
  CCo = concept c
    c is Co

  CCoChecked = concept c
    c is CCo
    explImpl(c) is CCo

implements CCo: X
#proc explImpl(t: X): CCo = t
#[
implements Co: int
implements Di: X
implements Di:
  type
    A = float
]#

let x = X(n: 3)
let y = Y[float](v: 3)

echo x is Co
echo x is CCoChecked
echo y is CCoChecked
echo x is CCo
echo y is CCo
echo explicitlyImplements(X, Co)
echo X.explicitlyImplements CCoChecked
#[
echo X.explicitlyImplements Di
echo int.explicitlyImplements Co
echo int.explicitlyImplements Di
echo A.explicitlyImplements Di
]#
proc print(c: CCo) = echo "Jepp"

print x
