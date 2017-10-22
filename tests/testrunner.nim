import explimpl, macros

type
  C = concept c
    c.n is int

  Ca = C

  Cd = distinct C

  X = object
    n: int

  Y = object
    n: int

  Z[T] = object
    x: T

explicit:
  type
    ExC = concept c
      c is C

implements C, ExC: X

implements C:
  type
    A = string
    Zs = Z[string]

assert(X.explicitlyImplements(C) == true)
assert(X.explicitlyImplements(Ca) == true)
assert(X.explicitlyImplements(Cd) == false)
assert(Y.explicitlyImplements(C) == false)
assert(Z[float].explicitlyImplements(C) == false)
assert(Zs.explicitlyImplements(C) == true)
assert(X.explicitlyImplements(ExC9F08B7C91364CDF2) == true)
assert(X is ExC == true)
