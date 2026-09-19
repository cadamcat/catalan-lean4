import Catalan.Stickelberger.RootDescent
import Catalan.Stickelberger.GaussIdentities
import Catalan.Stickelberger.GaloisCover

set_option autoImplicit false
noncomputable section
namespace Catalan.Stickelberger
open NumberField

 theorem exists_descended_gaussSum_mul_eq
    (p ell f : ℕ) [NeZero p] [Fact ell.Prime]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L] [IsGalois K L]
    {ζK : K} (hζK : IsPrimitiveRoot ζK p)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 L)) (hχ : χ ≠ 1)
    {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ ell)
    (hcard : Fintype.card F = ell ^ f)
    (hχp : ∀ x : F, x ≠ 0 → (χ x) ^ p = 1)
    (γ : 𝓞 K)
    (hγ : algebraMap (𝓞 K) (𝓞 L) γ = (integralTraceGaussSum χ hζ.pow_eq_one) ^ p) :
    ∃ γ' : 𝓞 K, γ * γ' = (ell : 𝓞 K) ^ (f * p) := by
  have hχinvp : ∀ x : F, x ≠ 0 → ((χ⁻¹) x) ^ p = 1 := by
    intro x hx
    rw [MulChar.inv_apply']
    exact hχp x⁻¹ (inv_ne_zero hx)
  have hχK : ∀ x : F, ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = χ x := by
    intro x
    by_cases hx : x = 0
    · subst x
      exact ⟨0, by simpa using (MulChar.map_zero χ).symm⟩
    · exact exists_ringOfIntegers_of_pow_eq_one p K L hζK (χ x) (hχp x hx)
  have hχinvK : ∀ x : F, ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = (χ⁻¹) x := by
    intro x
    by_cases hx : x = 0
    · subst x
      exact ⟨0, by simpa using (MulChar.map_zero (χ⁻¹)).symm⟩
    · exact exists_ringOfIntegers_of_pow_eq_one p K L hζK ((χ⁻¹) x) (hχinvp x hx)
  obtain ⟨γ', hγ'⟩ :=
    exists_ringOfIntegers_gaussSum_pow p ell K L (χ⁻¹) hζ
      (Fact.out : ell.Prime).one_lt hχinvp hχinvK
  have hminus : (χ (-1 : F)) ^ p = 1 := hχp (-1) (by simp)
  refine ⟨γ', ?_⟩
  apply (RingOfIntegers.algebraMap.injective K L)
  simpa only [map_mul, hγ, hγ', map_pow, map_natCast] using
    (integralTraceGaussSum_pow_mul_inv_pow (A := 𝓞 L) χ hχ hζ p f hcard hminus)

 theorem descended_gaussSum_emultiplicity_eq_zero_of_not_conj
    (p ell f : ℕ) [NeZero p] [Fact ell.Prime]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L] [IsGalois K L] [IsGalois ℚ K]
    {ζK : K} (hζK : IsPrimitiveRoot ζK p)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 L)) (hχ : χ ≠ 1)
    {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ ell)
    (hcard : Fintype.card F = ell ^ f)
    (hχp : ∀ x : F, x ≠ 0 → (χ x) ^ p = 1)
    (γ : 𝓞 K)
    (hγ : algebraMap (𝓞 K) (𝓞 L) γ = (integralTraceGaussSum χ hζ.pow_eq_one) ^ p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (ell : 𝓞 K) ∈ P)
    (Q : Ideal (𝓞 K)) [Q.IsMaximal]
    (hne : ∀ τ : K ≃ₐ[ℚ] K, Ideal.map (Catalan.integerAut K τ).toRingHom P ≠ Q) :
    emultiplicity Q (Ideal.span {γ}) = 0 := by
  obtain ⟨γ', hprod⟩ :=
    exists_descended_gaussSum_mul_eq p ell f K L hζK χ hχ hζ hcard hχp γ hγ
  exact emultiplicity_eq_zero_of_not_conj K ell (f * p) (Fact.out : ell.Prime)
    P hP (γ := γ) (γ' := γ') (u := 1) isUnit_one (by simpa using hprod) Q hne

end Catalan.Stickelberger
