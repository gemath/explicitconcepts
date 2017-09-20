import contracts, macros

type
  Co = concept c
    c.n is int

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

type
  CoF = concept c of Co

  CoC = concept c of CoF
    explImpl(c) is CoF

  DsF = concept c of Ds

  DsC = concept c of DsF
    explImpl(c) is DsF

implements CoF: X
implements CoF: Y
implements Co: int
implements DsF:
  type
    A = string

let
  x = X(n: 1)
  y = Y(n: 2)
  w = W(v: 4.0)
  a: A = "five"
  i: int = 6

echo x is Co
echo x is CoC
echo y is Co
echo y is CoC
echo w is Co
echo w is CoC
echo a is DsC

proc print(c: CoC) = echo "Jepp: ", c.n

print y

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
macro explicit(arg: untyped): NimNode =
  echo "bla -----------------------"
  newEmptyNode()

displayTree:
  type
    MyContract2 = explicit Co

  explicit MyContract c:
    c.f is bool
 
