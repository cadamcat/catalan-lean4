module

public import Catalan.Final.Assembly

/-!
# `Verification.Supplemental.strict.results.official-audit.Audit0001`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @Catalan.catalans_conjecture
#print Catalan.catalans_conjecture
set_option pp.universes false in
#print axioms Catalan.catalans_conjecture
