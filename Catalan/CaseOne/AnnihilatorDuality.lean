import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction
variable {R : Type*} [CommRing R] [IsSemisimpleRing R]

omit [IsSemisimpleRing R] in
private lemma annihilator_span_idempotent (e : R) (he : IsIdempotentElem e) :
    (Ideal.span ({e} : Set R)).annihilator = Ideal.span ({1 - e} : Set R) := by
  ext x
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_span_singleton]
  simp only [smul_eq_mul]
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    rw [mul_sub, mul_one, hx, sub_zero]
  · rintro ⟨a, rfl⟩
    rw [mul_assoc, he.one_sub_mul_self, mul_zero]

lemma semisimple_ideal_double_annihilator (I : Ideal R) :
    I.annihilator.annihilator = I := by
  obtain ⟨e, he, rfl⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  rw [annihilator_span_idempotent e he, annihilator_span_idempotent (1 - e) he.one_sub,
    sub_sub_cancel]

lemma semisimple_ideal_annihilator_mul (I J : Ideal R) :
    (I * J).annihilator = I.annihilator ⊔ J.annihilator := by
  obtain ⟨e, he, rfl⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  obtain ⟨f, hf, rfl⟩ := IsSemisimpleRing.ideal_eq_span_idempotent J
  rw [Ideal.span_singleton_mul_span_singleton, annihilator_span_idempotent (e * f) (he.mul hf),
    annihilator_span_idempotent e he, annihilator_span_idempotent f hf]
  apply le_antisymm
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Submodule.mem_sup.mpr
    refine ⟨1 - e, Ideal.subset_span (by simp), e * (1 - f),
      Ideal.mul_mem_left _ e (Ideal.subset_span (by simp)), ?_⟩
    ring
  · apply sup_le
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨1 - e, ?_⟩
      change (1 - e) * (1 - e * f) = 1 - e
      calc
        (1 - e) * (1 - e * f) = (1 - e) - ((1 - e) * e) * f := by ring
        _ = 1 - e := by rw [he.one_sub_mul_self, zero_mul, sub_zero]
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨1 - f, ?_⟩
      change (1 - f) * (1 - e * f) = 1 - f
      calc
        (1 - f) * (1 - e * f) = (1 - f) - e * ((1 - f) * f) := by ring
        _ = 1 - f := by rw [hf.one_sub_mul_self, mul_zero, sub_zero]

end Catalan.UnitReduction
