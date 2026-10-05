module

public import Catalan.StrictSolution

/-!
# `Verification.Supplemental.source.results.official-audit.Audit0008`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @StrictCatalan.signed_int
#print StrictCatalan.signed_int
set_option pp.universes false in
#print axioms StrictCatalan.signed_int
