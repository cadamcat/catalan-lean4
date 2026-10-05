module

public import Catalan.Stickelberger.NormalizedCharacter
public import Catalan.Stickelberger.GaussFamily
public import Catalan.Stickelberger.TowerArith
public import Catalan.Stickelberger.RootDescent

/-!
# `Catalan.Stickelberger.CharacterBridge`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Stickelberger
open NumberField

/-- Reduction is injective on roots of a fixed order when a primitive root stays primitive. -/
theorem eq_of_map_eq_of_pow_eq_one
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    {p : ℕ} [NeZero p] (π : A →+* B) {μ : A}
    (hμ : IsPrimitiveRoot μ p) (hπμ : IsPrimitiveRoot (π μ) p)
    {x y : A} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : π x = π y) : x = y := by
  obtain ⟨i, hi, hxi⟩ := hμ.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, hyj⟩ := hμ.eq_pow_of_pow_eq_one hy
  have he : (π μ) ^ i = (π μ) ^ j := by simpa [← map_pow, hxi, hyj] using hxy
  rw [← hxi, ← hyj, hπμ.pow_inj hi hj he]

/-- An order-p character constructed downstairs is the normalized member of the upstairs family. -/
theorem exists_baseChar_eq_invTeichmuller_pow
    (p : ℕ) [hp : Fact p.Prime]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsCyclotomicExtension {p} ℚ K]
    {F : Type*} [Field F] [Fintype F]
    (π : 𝓞 L →+* F) (hdiv : p ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot (π (algebraMap (𝓞 K) (𝓞 L) (Catalan.ζ_spec p K).toInteger)) p)
    (τ : MulChar F (𝓞 L)) (hred : ∀ x : F, π (τ x) = x⁻¹) :
    ∃ χ : MulChar F (𝓞 K), orderOf χ = p ∧
      χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L)) = τ ^ ((Fintype.card F - 1) / p) := by
  have instLocal1 : NeZero p := ⟨hp.out.ne_zero⟩
  let μ := (Catalan.ζ_spec p K).toInteger
  let μL := algebraMap (𝓞 K) (𝓞 L) μ
  have hμL : IsPrimitiveRoot μL p :=
    (Catalan.ζ_spec p K).toInteger_isPrimitiveRoot.map_of_injective
      (RingOfIntegers.algebraMap.injective K L)
  obtain ⟨ψ, hψ, hn⟩ := Catalan.exists_normalized_powerResidueChar F (𝓞 K) p hdiv
    (π.comp (algebraMap (𝓞 K) (𝓞 L))) (Catalan.ζ_spec p K).toInteger_isPrimitiveRoot hμ
  let χ := ψ⁻¹
  have hχord : orderOf χ = p := by simpa [χ] using hψ
  refine ⟨χ, hχord, ?_⟩
  have hχpow : χ ^ p = 1 := hχord ▸ pow_orderOf_eq_one χ
  have ht := (invTeichmuller_pow_normalization π τ hred p hdiv).1
  apply MulChar.ext
  intro u
  apply eq_of_map_eq_of_pow_eq_one π hμL hμ
  · rw [MulChar.ringHomComp_apply, ← map_pow]
    have hu := DFunLike.congr_fun hχpow (u : F)
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe, map_one] using
      congrArg (algebraMap (𝓞 K) (𝓞 L)) hu
  · have hu := DFunLike.congr_fun ht (u : F)
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hu
  · rw [MulChar.ringHomComp_apply]
    change (π.comp (algebraMap (𝓞 K) (𝓞 L))) (ψ⁻¹ (u : F)) = _
    rw [MulChar.inv_apply']
    have hninv := hn u⁻¹
    simp only [Units.val_inv_eq_inv_val, inv_pow] at hninv
    rw [hninv]
    exact (invTeichmuller_pow_normalization π τ hred p hdiv).2 u |>.symm

end Catalan.Stickelberger
