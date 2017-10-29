import explicitconcepts, macros

type
  C = concept c
    c.n is int

  Ca = C

  Cd = distinct C

  Crt = concept c of C
    c is C

  Cr = concept c of C
    c.x is float

  X* = object of RootObj
    n*: int

  Xa = X

  Xd = distinct X

  Z[T] = object
    x: T

# Defines explicit concepts. 
explicit:
  type
    # The explicit version of an existing concept under a new name.
    ExC* = distinct C

    ExD = concept d
      d.x is float

# Defines implements-relationships for an existing type: X implements C and
# ExC. C is not explicit, so the compiler will warn about it.
implements C, ExC: X

# Redundant implements-statements are ignored and warned about.
implements ExC: X

# Defines implements-relationships for new types: Xx and Y implement ExD.
implements ExD:
  type
    Xx = object of X
      x: float

    Y = object of RootObj
      x: float

# This blatant lie (X doesn't even satisfy ExD) should explode:
# TODO: how do I test this?
#assert(not compiles(implements ExD: X), "This should not compile!")

# Generic type instances are supported as implementers. Generic concepts are
# not yet supported.
implements ExD: Z[float]

type
  Yn* = object of Y
    n*: int

  ExDr = concept d of ExD
    d.n is int

explicit:
  type
    ExDrx = concept d of ExD
      d.n is int

proc run*() =
  # Make sure that implements-relationships registered correctly ..
  assert(X.checkImplements(C) == true)
  assert(X.checkImplements(ExC) == true)
  assert(Xx.checkImplements(ExD) == true)
  assert(Y.checkImplements(ExD) == true)
  assert(Z[float].checkImplements(ExD) == true)

  # .. and that there is no false positive.
  assert(Yn.checkImplements(C) == false)

  # Implements-relationships extend to aliases ..
  assert(X.checkImplements(Ca) == true)
  assert(Xa.checkImplements(C) == true)

  # .. and to derivatives of the implementing type ..
  assert(Xx.checkImplements(C) == true)

  # .. but not to distinct aliases ..
  assert(X.checkImplements(Cd) == false)
  assert(Xd.checkImplements(C) == false)

  # .. or refinements of an implemented concept.
  assert(X.checkImplements(Crt) == false)
  assert(Xx.checkImplements(ExDr) == false)

  # Both types technically satisfy the concept, but the concept is explicit and
  # only X has an implements-relationship with it.
  assert(X is ExC)
  assert(not(Yn is ExC))

  # Also, being explicit is not just passed on to a refined concept ..
  assert(Xx is ExDr)

  # .. but the refined concept itself has to be made explicit.
  assert(not(Xx is ExDrx))

  # 
  # The additional stand-in concept generated for an explicit concept (for
  # internal use, note the "magic" postfix).
  assert(X.checkImplements(ExC9F08B7C91364CDF2) == true)
