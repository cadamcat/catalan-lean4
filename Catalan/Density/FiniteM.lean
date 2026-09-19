import Catalan.Density.BaseFields

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma finiteDimensional_Msub (p q : ℕ) (hq : 0 < q) :
    FiniteDimensional (F p) (Msub p q) := by
  classical
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  have instNeZeroQ : NeZero q := ⟨hq.ne'⟩
  obtain ⟨S, hS, hSfin⟩ :=
    (Monoid.fg_iff (M := (NumberField.RingOfIntegers (F p))ˣ)).mp inferInstance
  let root : (NumberField.RingOfIntegers (F p))ˣ → Omega := fun u =>
    Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (algebraMap (F p) Omega (((u : NumberField.RingOfIntegers (F p)) : F p))) hq)
  have hroot (u : (NumberField.RingOfIntegers (F p))ˣ) :
      root u ^ q = algebraMap (F p) Omega
        (((u : NumberField.RingOfIntegers (F p)) : F p)) :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq _ hq)
  let E : IntermediateField (F p) Omega :=
    Bsub p q ⊔ IntermediateField.adjoin (F p) (root '' S)
  have instFiniteRootSet : Finite (root '' S) := (hSfin.image root).to_subtype
  have instFiniteRootField :
      FiniteDimensional (F p) (IntermediateField.adjoin (F p) (root '' S)) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro r _
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).isIntegral.tower_top
  have instFiniteE : FiniteDimensional (F p) E :=
    IntermediateField.finiteDimensional_sup _ _
  have hB : Bsub p q ≤ E := le_sup_left
  have hRootField : IntermediateField.adjoin (F p) (root '' S) ≤ E := le_sup_right
  have hgen (u : (NumberField.RingOfIntegers (F p))ˣ) (hu : u ∈ S) : root u ∈ E :=
    hRootField (IntermediateField.subset_adjoin (F p) (root '' S) ⟨u, hu, rfl⟩)
  have hunit (u : (NumberField.RingOfIntegers (F p))ˣ) :
      ∃ t : Omega, t ∈ E ∧ t ^ q = algebraMap (F p) Omega
        (((u : NumberField.RingOfIntegers (F p)) : F p)) := by
    have hu : u ∈ Submonoid.closure S := by rw [hS]; trivial
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact ⟨root u, hgen u hu, hroot u⟩
    | one => exact ⟨1, E.one_mem, by simp⟩
    | mul u v hu hv ihu ihv =>
      obtain ⟨s, hs, hsPow⟩ := ihu
      obtain ⟨t, ht, htPow⟩ := ihv
      refine ⟨s * t, E.mul_mem hs ht, ?_⟩
      rw [mul_pow, hsPow, htPow]
      simp
  have hzeta : primitiveRoot q ∈ E :=
    hB (IntermediateField.subset_adjoin (F p) _ (Set.mem_singleton _))
  have hrad : unitRadicals p q ⊆ E := by
    rintro r ⟨u, hrPow⟩
    change r ∈ E
    obtain ⟨t, ht, htPow⟩ := hunit u
    have ht0 : t ≠ 0 := by
      intro ht0
      have huF : ((u : NumberField.RingOfIntegers (F p)) : F p) = 0 := by
        apply (algebraMap (F p) Omega).injective
        rw [map_zero, ← htPow, ht0, zero_pow hq.ne']
      have huO : (u : NumberField.RingOfIntegers (F p)) = 0 := by
        apply Subtype.ext
        exact huF
      exact Units.ne_zero u huO
    have hratio : (r / t) ^ q = 1 := by
      rw [div_pow, hrPow, ← htPow, div_self (pow_ne_zero q ht0)]
    obtain ⟨i, hi, hratioPow⟩ := (primitiveRoot_spec q hq).eq_pow_of_pow_eq_one hratio
    have hratiomem : r / t ∈ E := hratioPow ▸ pow_mem hzeta i
    simpa only [div_mul_cancel₀ r ht0] using E.mul_mem hratiomem ht
  have hME : Msub p q ≤ E :=
    sup_le hB (IntermediateField.adjoin_le_iff.mpr hrad)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hME).toLinearMap
    (IntermediateField.inclusion_injective hME)

lemma numberField_Msub (p q : ℕ) (hq : 0 < q) : NumberField (Msub p q) := by
  have instFiniteM : FiniteDimensional (F p) (Msub p q) := finiteDimensional_Msub p q hq
  exact NumberField.of_module_finite (F p) (Msub p q)

end Catalan.A3
