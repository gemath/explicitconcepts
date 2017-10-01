import explimpl, macros

type
  Co = concept c
    c.n is int

  Coa = Co

  Cod = distinct Co

  D[T] = concept d
    d.v is T

  Di = D[int]
  Ds = D[string]

  W = object
    v: float

  X = object
    n: int

  Y = object
    n: int

  CoF = concept c of Co

  CoC = concept c of CoF
    explImpl(c) is CoF

  DsF = concept c of Ds
    c is Ds

  DsC = concept c of DsF
    explImpl(c) is DsF

#implements CoF: X
#implements CoF: Y
#implements Cod: X
implements Co: X

implements Co:
  type
    A = string

    Z[T] = object
      x: T

    Zs = Z[string]

echo Z.explicitlyImplements(Co)
echo Zs.explicitlyImplements(Co)
echo X.explicitlyImplements(Co)
echo X.explicitlyImplements(Coa)
echo X.explicitlyImplements(Cod)

let
  x = X(n: 1)
  y = Y(n: 2)
  w = W(v: 4.0)
#  a: A = "five"
  i: int = 6

proc print(c: Cod) = echo "Jepp: ", c.n

#print x

#[
  nnkTypeClassTy.newTree(
    nnkArglist.newTree(
      newIdentNode(!"c")
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkStmtList.newTree(
      nnkInfix.newTree(
        newIdentNode(!"is"),
        nnkDotExpr.newTree(
          newIdentNode(!"c"),
          newIdentNode(!"f")
        ),
        newIdentNode(!"bool")
      )
    )
  )
]#
