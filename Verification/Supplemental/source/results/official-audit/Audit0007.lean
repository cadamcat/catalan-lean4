module

public import Catalan.StrictSolution

/-!
# `Verification.Supplemental.source.results.official-audit.Audit0007`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @StrictCatalan.positive_int
#print StrictCatalan.positive_int
set_option pp.universes false in
#print axioms StrictCatalan.positive_int
