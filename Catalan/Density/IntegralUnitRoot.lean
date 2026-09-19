import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Kummer

lemma exists_integralUnit_of_field_root
    (L : Type*) [Field L] [NumberField L] (q : ℕ) (hq : 0 < q)
    (u : (𝓞 L)ˣ) (r : L) (hr : r ^ q = ((u : 𝓞 L) : L)) :
    ∃ rO : (𝓞 L)ˣ, ((rO : 𝓞 L) : L) = r ∧ rO ^ q = u := by
  have hint : IsIntegral ℤ r := IsIntegral.of_pow hq (by
    rw [hr]
    exact (u : 𝓞 L).isIntegral_coe)
  let R : 𝓞 L := ⟨r, hint⟩
  have hR : R ^ q = (u : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    change r ^ q = ((u : 𝓞 L) : L)
    exact hr
  have hunit : IsUnit R := (isUnit_pow_iff hq.ne').mp (hR ▸ u.isUnit)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [hunit.unit_spec]
    rfl
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hunit.unit_spec, hR]

end Catalan.Kummer
