import explicitconcepts
import test

type
  C = concept c
    c.n is int

# Implements-relationships and "explicitness" of concepts are public, check
# wether they are  imported from another module. Qualified identifiers should
# work as expected.
assert(X is test.ExC == true)
assert(Yn is ExC == false)

# C is not exported by test, a local copy is used instead ..
assert(X is C == true)

# .. which has no implements-relation to X ..
assert(X.checkImplements(C) == false)

# .. until one is established locally.
implements C: X
assert(X.checkImplements(C) == true)
