module

public import Catalan.JSP

/-!
# `Verification.Supplemental.strict.results.official-audit.Audit0000`

Verification support module.
-/

@[expose] public section

set_option pp.all true
#check @Catalan.JSP.statement
#print Catalan.JSP.statement
set_option pp.universes false in
#print axioms Catalan.JSP.statement
