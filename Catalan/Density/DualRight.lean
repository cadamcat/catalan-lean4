module

public import Catalan.Density.PairingDual
public import Catalan.Density.FixedRoot

/-!
# `Catalan.Density.DualRight`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma kummerFunctional_right_nondegenerate (p q : ℕ) [Fact q.Prime]
    (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q)
    (hz : ∀ σ : Msub p q ≃ₐ[Bsub p q] Msub p q, kummerFunctional p q σ z = 0) :
    z = 0 := by
  induction z using QuotientGroup.induction_on with
  | _ u =>
    obtain ⟨v, hv⟩ := unit_qth_root_of_all_aut_fix_unitRoot p q u (by
      intro σ
      exact (kummerValue_eq_one_iff p q σ u).mp
        ((kummerFunctional_apply_eq_zero_iff p q σ u).mp (hz σ)))
    change (QuotientGroup.mk u : (𝓞 (F p))ˣ ⧸ UnitQuotient.qPowers (𝓞 (F p))ˣ q) = 1
    exact (QuotientGroup.eq_one_iff u).mpr ⟨v, hv⟩

end Catalan.A3
