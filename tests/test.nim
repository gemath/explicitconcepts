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

# Defines implements-relations for an existing type: X implements C and
# ExC. C is not explicit, so the compiler will warn about it.
implements C, ExC: X

# An allegedly implementing type not (yet) satisfying the concept is warned about.
implements ExD: X

# Redundant implements-statements are ignored and warned about.
implements ExC: X

# Defines implements-relations for new types: Xx and Y implement ExD.
implements ExD:
  type
    Xx = object of X
      x: float

    Y = object of RootObj
      x: float

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
    ExDrx = distinct ExD

proc run*() =
  # Make sure implements-relations registered correctly ..
  assert X.checkImplements(C)
  assert X.checkImplements(ExC)
  assert Xx.checkImplements(ExD)
  assert Y.checkImplements(ExD)
  assert Z[float].checkImplements(ExD)

  # .. and that this is no false positive.
  assert(not Yn.checkImplements(C))

  # Implements-relations extend to aliases ..
  assert X.checkImplements(Ca)
  assert Xa.checkImplements(C)

  # .. and to derivatives of the implementing type ..
  assert Xx.checkImplements(C)

  # .. but not to distinct aliases ..
  assert(not X.checkImplements(Cd))
  assert(not Xd.checkImplements(C))

  # .. or refinements of an implemented concept.
  assert(not X.checkImplements(Crt))
  assert(not Xx.checkImplements(ExDr))

  # X is not a concept.
  assert(not(compiles do:
    implements X: Xx
  ))

  # These two types technically satisfy the concept, but the concept is
  # explicit and only X has an implements-relation with it.
  assert(X is ExC)
  assert(not(Yn is ExC))

  # Aliases cannot be explicit.
  assert(not(compiles do:
    explicit:
      type ExCa = ExC
  ))

  # Also, being explicit is not just passed on to a refined concept ..
  assert(Xx is ExDr)

  # .. but a distinct alias has to be made explicit.
  assert(not(Xx is ExDrx))

  # An implements-relation to an explicit concept extends to all explicit base
  # concepts.
  #assert(compiles do:
  #  implements ExDrx: Yn
  #)
  #assert(Yn is ExD)
