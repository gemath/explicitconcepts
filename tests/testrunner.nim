import test, explicitconcepts

type
  C = concept c
    c.n is int

run()

# Implements-relationships and "explicitness" of concepts are public and can
# be provided by imported modules. Qualified identifiers are supported.
assert(X is test.ExC == true)
assert(Yn is ExC == false)

# C is not exported by test, a local copy is used instead ..
assert(X is C == true)

# .. which has no implements-relation to X ..
assert(X.checkImplements(C) == false)

# .. until 
