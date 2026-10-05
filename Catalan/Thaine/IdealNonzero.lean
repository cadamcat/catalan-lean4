module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# `Catalan.Thaine.IdealNonzero`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Thaine

lemma ideal_triple_product_ne_bot
    (A : Type*) [CommRing A] (B I M J : Ideal A)
    (hB : B.annihilator = (I * M) * J)
    (hIM : I ⊔ M = ⊤) (hJM : J ⊔ M = ⊤) (hM : M ≠ ⊤) :
    (B * I) * J ≠ ⊥ := by
  intro hzero
  have hsmul : (I * J) • B = ⊥ := by
    rw [Ideal.smul_eq_mul]
    calc
      (I * J) * B = (B * I) * J := by ac_rfl
      _ = ⊥ := hzero
  have hann : I * J ≤ B.annihilator :=
    (Submodule.le_annihilator_iff).2 hsmul
  have hmul : I * J = (I * J) * M := by
    apply le_antisymm
    · calc
        I * J ≤ (I * M) * J := by simpa only [hB] using hann
        _ = (I * J) * M := by ac_rfl
    · exact Ideal.mul_le_left
  have hsub : I * J ≤ M := by
    rw [hmul]
    exact Ideal.mul_le_right
  have htop : I * J ⊔ M = ⊤ := by
    calc
      I * J ⊔ M = J ⊔ M :=
        Ideal.mul_sup_eq_of_coprime_left (I := I) (J := M) (K := J) hIM
      _ = ⊤ := hJM
  have hle : ⊤ ≤ M := by
    rw [← htop]
    exact sup_le hsub le_rfl
  exact hM (top_le_iff.mp hle)

end Catalan.Thaine
