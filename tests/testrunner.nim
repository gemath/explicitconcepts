import test

run()

# Implements-relationships and "explicitness" of concepts are public and can
# be provided by imported modules.
assert(X is ExC == true)
assert(Yn is ExC == false)
