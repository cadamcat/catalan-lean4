module

/-!
# `Verification.Supplemental.common.audit.controls.extra-axiom.Fixture.Solution`

Verification support module.
-/

@[expose] public section

namespace StrictControl
axiom forbidden_assumption : True
theorem target : True := forbidden_assumption
end StrictControl
