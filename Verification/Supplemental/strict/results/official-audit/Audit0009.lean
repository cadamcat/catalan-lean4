module

public import Catalan.StrictSolution

/-!
# `Verification.Supplemental.strict.results.official-audit.Audit0009`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @StrictCatalan.odd_primes
#print StrictCatalan.odd_primes
set_option pp.universes false in
#print axioms StrictCatalan.odd_primes
