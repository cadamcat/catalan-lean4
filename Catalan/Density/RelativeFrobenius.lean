import Catalan.Density.FrobeniusStabilizer

set_option autoImplicit false
open NumberField
open scoped Pointwise
noncomputable section
namespace Catalan.A3

theorem integerAutSMulCommClass (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm sigma a b := by
    apply RingOfIntegers.coe_injective
    change sigma (algebraMap K L (a : K) * (b : L)) =
      algebraMap K L (a : K) * sigma (b : L)
    rw [map_mul, sigma.commutes]

attribute [local instance] integerAutSMulCommClass

lemma preservesPrime_iff_mem_zpowers_of_nativeFrob
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (P : Ideal (𝓞 L)) (hPmax : P.IsMaximal) (hPbot : P ≠ ⊥)
    (rho : L ≃ₐ[K] L) (hunram : InertiaTrivial K L P)
    (hfrob : IsArithFrobAt (𝓞 K) rho P) (tau : L ≃ₐ[K] L) :
    PreservesPrime tau P ↔ tau ∈ Subgroup.zpowers rho := by
  classical
  have instMaxP : P.IsMaximal := hPmax
  let instBaseField : Field (𝓞 K ⧸ P.under (𝓞 K)) := Ideal.Quotient.field _
  let instResidueField : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  have instFiniteResidue : Finite (𝓞 L ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hPbot
  have instFiniteBase : Finite (𝓞 K ⧸ P.under (𝓞 K)) :=
    Finite.of_injective _ Ideal.algebraMap_quotient_injective
  obtain ⟨ell, instCharEll⟩ := CharP.exists (𝓞 K ⧸ P.under (𝓞 K))
  have instPrimeEll : Fact ell.Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ P.under (𝓞 K)) ell⟩
  let D := MulAction.stabilizer (L ≃ₐ[K] L) P
  let f : D →* ((𝓞 L ⧸ P) ≃ₐ[𝓞 K ⧸ P.under (𝓞 K)] (𝓞 L ⧸ P)) :=
    Ideal.Quotient.stabilizerHom P (P.under (𝓞 K)) (L ≃ₐ[K] L)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro delta hdelta
    apply Subtype.ext
    apply hunram delta.val
    · exact (preservesPrime_iff_mem_stabilizer K L delta.val P).mpr delta.property
    · intro x
      have hx := DFunLike.congr_fun hdelta (Ideal.Quotient.mk P x)
      change Ideal.Quotient.mk P (integralAut delta.val x) = Ideal.Quotient.mk P x at hx
      exact Ideal.Quotient.eq.mp hx
  have hr : rho ∈ D := hfrob.mem_stabilizer
  let r : D := ⟨rho, hr⟩
  let n : ℕ := Nat.card (𝓞 K ⧸ P.under (𝓞 K))
  have hfr (x : 𝓞 L ⧸ P) : f r x = x ^ n := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk P (integralAut rho x) = (Ideal.Quotient.mk P x) ^ n
    rw [← map_pow, Ideal.Quotient.eq]
    exact hfrob x
  have hfrpow (i : ℕ) (x : 𝓞 L ⧸ P) : f (r ^ i) x = x ^ (n ^ i) := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', map_mul]
      change f r (f (r ^ i) x) = x ^ (n ^ (i + 1))
      rw [hfr, hi, ← pow_mul, pow_succ]
  constructor
  · intro htau
    let t : D := ⟨tau, (preservesPrime_iff_mem_stabilizer K L tau P).mp htau⟩
    obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow
      (𝓞 K ⧸ P.under (𝓞 K)) ell (𝓞 L ⧸ P) (f t)
    have heq : t = r ^ i := hf (by
      apply AlgEquiv.ext
      intro x
      rw [hi, hfrpow])
    have hval : tau = rho ^ i := congrArg Subtype.val heq
    rw [hval]
    exact Subgroup.pow_mem (Subgroup.zpowers rho) (Subgroup.mem_zpowers rho) i
  · intro htau
    apply (preservesPrime_iff_mem_stabilizer K L tau P).mpr
    exact (Subgroup.zpowers_le.mpr hr) htau

end Catalan.A3
