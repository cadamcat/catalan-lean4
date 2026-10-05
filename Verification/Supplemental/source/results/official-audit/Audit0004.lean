module

public import Catalan.Final.Assembly

/-!
# `Verification.Supplemental.source.results.official-audit.Audit0004`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @Catalan.mihailescu_odd_primes
#print Catalan.mihailescu_odd_primes
set_option pp.universes false in
#print axioms Catalan.mihailescu_odd_primes
