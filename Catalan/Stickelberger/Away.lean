module

public import Catalan.IdealHelpers

/-!
# `Catalan.Stickelberger.Away`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField
noncomputable section
namespace Catalan

lemma fractionalIdealUnit_pow_injective (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun J : FracIdealUnit K => J ^ n) := by
  intro I J h
  apply Units.ext
  have hc (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      FractionalIdeal.count K v (I : FracIdeal K) =
        FractionalIdeal.count K v (J : FracIdeal K) := by
    have hh := congrArg (fun U : FracIdealUnit K =>
      FractionalIdeal.count K v (U : FracIdeal K)) h
    simp only [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow] at hh
    exact mul_left_cancel₀ (by exact_mod_cast hn : (n : ℤ) ≠ 0) hh
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero J)]
  simp_rw [hc]

lemma principalIdeal_of_pow_eq (K : Type*) [Field K] [NumberField K]
    (J : FracIdealUnit K) (γ : Kˣ) (n : ℕ) (hn : n ≠ 0)
    (h : J ^ n = principalIdeal K (γ ^ n)) :
    J = principalIdeal K γ := by
  apply fractionalIdealUnit_pow_injective K n hn
  simpa only [map_pow] using h

lemma idealUnit_principal_of_isPrincipalIdealRing (K : Type*) [Field K] [NumberField K]
    [IsPrincipalIdealRing (𝓞 K)] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ γ : Kˣ, idealUnit K I hI = principalIdeal K γ := by
  obtain ⟨a, ha⟩ := (Submodule.IsPrincipal.principal (S := I))
  have hIa : I = Ideal.span {a} := ha
  have ha0 : (a : K) ≠ 0 := by
    have : a ≠ 0 := by
      intro h; apply hI; simp [hIa, h]
    exact_mod_cast this
  refine ⟨Units.mk0 (a : K) ha0, ?_⟩
  apply Units.ext
  rw [coe_idealUnit, hIa, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

lemma isPrincipalIdealRing_cyclotomic_two (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have hdim : Module.finrank ℚ K = 1 := by
    simpa using IsCyclotomicExtension.Rat.finrank 2 K
  obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hdim
  let eZ : ℤ ≃+* 𝓞 K := Rat.ringOfIntegersEquiv.symm.trans
    (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)
  exact IsPrincipalIdealRing.of_surjective eZ eZ.surjective

lemma prime_generator_away_two (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2} ℚ K]
    (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥) (k : ℕ) :
    ∃ γ : Kˣ, ipow 2 K (idealUnit K I hI0) (ΘS 2 K k) =
      principalIdeal K γ := by
  let := isPrincipalIdealRing_cyclotomic_two K
  obtain ⟨δ, hδ⟩ := idealUnit_principal_of_isPrincipalIdealRing K I hI0
  refine ⟨(ΘS 2 K k).coeff.prod (fun τ m => (elementAct K τ δ) ^ m), ?_⟩
  rw [hδ, ipow_principalIdeal]

/-- A Gauss eigenvector with p-th-root eigenvalues has its p-th power in
    the base field. This is the fixed-field part of Gauss-power descent. -/
lemma exists_descended_gauss_power
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsGalois K E] [FiniteDimensional K E]
    (g : E) (hg : g ≠ 0) (p : ℕ)
    (c : (E ≃ₐ[K] E) → E)
    (heigen : ∀ τ, τ g = c τ * g) (hc : ∀ τ, c τ ^ p = 1) :
    ∃ Γ : Kˣ, algebraMap K E (Γ : K) = g ^ p := by
  have hfixed (τ : E ≃ₐ[K] E) : τ (g ^ p) = g ^ p := by
    rw [map_pow, heigen τ, mul_pow, hc τ, one_mul]
  obtain ⟨Γ, hΓ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := E) (g ^ p)).mpr hfixed
  have hΓ0 : Γ ≠ 0 := by
    intro h
    have : g ^ p = 0 := by rw [← hΓ, h, map_zero]
    exact (pow_ne_zero p hg) this
  exact ⟨Units.mk0 Γ hΓ0, hΓ⟩

/-- The quotient of two Gauss eigenvectors descends when the lifted cyclotomic
    automorphism raises each eigenvalue to the corresponding power. -/
lemma exists_descended_gauss_quotient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsGalois K E] [FiniteDimensional K E]
    (g : E) (hg : g ≠ 0) (s : E ≃+* E) (σ : K ≃+* K)
    (k p : ℕ) (Γ : K)
    (hlift : ∀ x : K, s (algebraMap K E x) = algebraMap K E (σ x))
    (hpower : g ^ p = algebraMap K E Γ)
    (c : (E ≃ₐ[K] E) → E)
    (heigen : ∀ τ, τ g = c τ * g)
    (hc : ∀ τ, s (c τ) = c τ ^ k)
    (hcomm : ∀ τ : E ≃ₐ[K] E, Function.Commute τ s) :
    ∃ δ : Kˣ, algebraMap K E (δ : K) = g ^ k / s g ∧
      (δ : K) ^ p = Γ ^ k / σ Γ := by
  have hfixed (τ : E ≃ₐ[K] E) : τ (g ^ k / s g) = g ^ k / s g := by
    have hc0 : c τ ≠ 0 := by
      intro h
      have hzero : τ g = 0 := by rw [heigen τ, h, zero_mul]
      exact hg (τ.injective (hzero.trans τ.map_zero.symm))
    rw [map_div₀, map_pow, hcomm τ g, heigen τ, map_mul, hc τ, mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hc0)
  obtain ⟨δ, hδ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := E) (g ^ k / s g)).mpr hfixed
  have hδ0 : δ ≠ 0 := by
    intro h
    have : g ^ k / s g = 0 := by rw [← hδ, h, map_zero]
    exact (div_ne_zero (pow_ne_zero k hg) (by simpa using hg)) this
  refine ⟨Units.mk0 δ hδ0, hδ, ?_⟩
  apply (algebraMap K E).injective
  change algebraMap K E (δ ^ p) = _
  rw [map_pow, hδ, div_pow, ← map_pow, ← pow_mul, Nat.mul_comm k p,
    pow_mul, hpower, hlift, map_div₀, map_pow]

/-- Once a descended element supplies the power identity, cancellation takes
    place in fractional ideals. No torsion claim about ideal classes is needed. -/
lemma ipow_principal_of_descended_power
    (p : ℕ) (K : Type*) [Field K] [NumberField K]
    (J : FracIdealUnit K) (Θ : R p K) (δ : Kˣ) (hp : p ≠ 0)
    (h : ipow p K J ((p : ℤ) • Θ) = principalIdeal K (δ ^ p)) :
    ipow p K J Θ = principalIdeal K δ := by
  apply principalIdeal_of_pow_eq K _ δ p hp
  simpa only [ipow_zsmul, zpow_natCast] using h

end Catalan
