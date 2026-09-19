import Catalan.Wieferich.Core

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitQuotient

lemma field_qth_root_of_coprime_degree
    (F L : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (q : ℕ) (hc : Nat.Coprime q (Module.finrank F L)) (a : F)
    (h : ∃ b : L, b ^ q = algebraMap F L a) :
    ∃ b : F, b ^ q = a := by
  obtain ⟨b, hb⟩ := h
  have hnorm := congrArg (Algebra.norm F) hb
  rw [map_pow, Algebra.norm_algebraMap] at hnorm
  obtain ⟨c, _, hca⟩ := (pow_eq_pow_iff_of_coprime hc).mp hnorm
  exact ⟨c, hca.symm⟩

lemma unit_qth_root_of_field_qth_root
    (F : Type*) [Field F] [NumberField F] (q : ℕ) (hq : 0 < q)
    (u : (𝓞 F)ˣ) (h : ∃ b : F, b ^ q = ((u : 𝓞 F) : F)) :
    ∃ v : (𝓞 F)ˣ, v ^ q = u := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨B, hB⟩ := A1e.integral_qth_root q hq (u : 𝓞 F) b hb
  have hBpow : IsUnit (B ^ q) := by rw [hB]; exact u.isUnit
  have hBunit : IsUnit B := (isUnit_pow_iff hq.ne').mp hBpow
  refine ⟨hBunit.unit, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hBunit.unit_spec, hB]

end Catalan.UnitQuotient
