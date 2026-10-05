module

public import Catalan.Density.Definitions

/-!
# `Catalan.Density.FrobeniusStabilizer`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
open scoped Pointwise
noncomputable section
namespace Catalan.A3

lemma preservesPrime_iff_mem_stabilizer
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (P : Ideal (𝓞 L)) :
    PreservesPrime σ P ↔ σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) P := by
  rw [MulAction.mem_stabilizer_iff]
  change (∀ x : 𝓞 L, σ • x ∈ P ↔ x ∈ P) ↔ σ • P = P
  constructor
  · intro h
    apply Ideal.ext
    intro x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simpa only [smul_inv_smul] using (h (σ⁻¹ • x)).symm
  · intro h x
    have hx := Ideal.smul_mem_pointwise_smul_iff (a := σ) (S := P) (x := x)
    rwa [h] at hx

lemma preservesPrime_iff_mem_zpowers_of_arithmeticFrob
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 L))
    (ρ : L ≃ₐ[ℚ] L) (hρ : IsArithmeticFrob ell P ρ)
    (τ : L ≃ₐ[ℚ] L) :
    PreservesPrime τ P ↔ τ ∈ Subgroup.zpowers ρ := by
  classical
  rcases hρ with ⟨hmax, hP0, hellP, hfinite, hinertia, hpresρ, hcong⟩
  have instPrimeEll : Fact ell.Prime := ⟨hell⟩
  have instMaxP : P.IsMaximal := hmax
  have hellInt : Prime (ell : ℤ) := Nat.prime_iff_prime_int.mp hell
  have instMaxEll : (Ideal.span {(ell : ℤ)}).IsMaximal := hellInt.isMaximal_span_singleton
  have instOver : P.LiesOver (Ideal.span {(ell : ℤ)}) :=
    (Ideal.liesOver_span_iff hmax.ne_top hellInt).mpr (by simpa using hellP)
  let instBaseField : Field (ℤ ⧸ Ideal.span {(ell : ℤ)}) := Ideal.Quotient.field _
  let instResidueField : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  have instCharEll : CharP (ℤ ⧸ Ideal.span {(ell : ℤ)}) ell :=
    ringChar.of_eq (Int.ringChar_idealQuot ell)
  have instFiniteResidue : Finite (𝓞 L ⧸ P) := hfinite
  let D := MulAction.stabilizer (L ≃ₐ[ℚ] L) P
  let f : D →* ((𝓞 L ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(ell : ℤ)}] (𝓞 L ⧸ P)) :=
    Ideal.Quotient.stabilizerHom P (Ideal.span {(ell : ℤ)}) (L ≃ₐ[ℚ] L)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro δ hδ
    apply Subtype.ext
    apply hinertia δ.val
    · exact (preservesPrime_iff_mem_stabilizer ℚ L δ.val P).mpr δ.property
    · intro x
      have hx := DFunLike.congr_fun hδ (Ideal.Quotient.mk P x)
      change Ideal.Quotient.mk P (integralAut δ.val x) = Ideal.Quotient.mk P x at hx
      exact Ideal.Quotient.eq.mp hx
  have hr : ρ ∈ D := (preservesPrime_iff_mem_stabilizer ℚ L ρ P).mp hpresρ
  let r : D := ⟨ρ, hr⟩
  have hfr (x : 𝓞 L ⧸ P) : f r x = x ^ ell := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk P (integralAut ρ x) = (Ideal.Quotient.mk P x) ^ ell
    rw [← map_pow, Ideal.Quotient.eq]
    exact hcong x
  have hfrpow (i : ℕ) (x : 𝓞 L ⧸ P) : f (r ^ i) x = x ^ (ell ^ i) := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', map_mul]
      change f r (f (r ^ i) x) = x ^ (ell ^ (i + 1))
      rw [hfr, hi, ← pow_mul, pow_succ]
  constructor
  · intro hτ
    let t : D := ⟨τ, (preservesPrime_iff_mem_stabilizer ℚ L τ P).mp hτ⟩
    obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow
      (ℤ ⧸ Ideal.span {(ell : ℤ)}) ell (𝓞 L ⧸ P) (f t)
    have heq : t = r ^ i := hf (by
      apply AlgEquiv.ext
      intro x
      rw [hi, Int.card_ideal_quot, hfrpow])
    have hval : τ = ρ ^ i := congrArg Subtype.val heq
    rw [hval]
    exact Subgroup.pow_mem (Subgroup.zpowers ρ) (Subgroup.mem_zpowers ρ) i
  · intro hτ
    apply (preservesPrime_iff_mem_stabilizer ℚ L τ P).mpr
    exact (Subgroup.zpowers_le.mpr hr) hτ

end Catalan.A3
