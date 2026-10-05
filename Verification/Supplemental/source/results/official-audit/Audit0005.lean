module

public import Catalan.StrictSolution

/-!
# `Verification.Supplemental.source.results.official-audit.Audit0005`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @StrictCatalan.jsp
#print StrictCatalan.jsp
set_option pp.universes false in
#print axioms StrictCatalan.jsp
