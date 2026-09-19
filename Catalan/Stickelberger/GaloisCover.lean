import Catalan.IdealAction
import Catalan.Stickelberger.Factor
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger
open NumberField

/-- Galois 传递性：数域 `K/ℚ` Galois 时，`ell` 上方的两个极大理想必是 Galois 共轭。 -/
theorem exists_integerAut_map_eq_of_natCast_mem
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (ell : ℕ) (hell : ell.Prime)
    (P Q : Ideal (𝓞 K)) [P.IsMaximal] [Q.IsMaximal]
    (hP : (ell : 𝓞 K) ∈ P) (hQ : (ell : 𝓞 K) ∈ Q) :
    ∃ τ : K ≃ₐ[ℚ] K, Ideal.map (Catalan.integerAut K τ).toRingHom P = Q := by
  have : Fact (Nat.Prime ell) := ⟨hell⟩
  let p : Ideal ℤ := Ideal.span {(ell : ℤ)}
  have hpmax : p.IsMaximal := by
    exact Int.ideal_span_isMaximal_of_prime ell
  have hPprime : P.IsPrime := Ideal.IsMaximal.isPrime (inferInstance : P.IsMaximal)
  have hQprime : Q.IsPrime := Ideal.IsMaximal.isPrime (inferInstance : Q.IsMaximal)
  have : P.IsPrime := hPprime
  have : Q.IsPrime := hQprime
  have hp_le_P : p ≤ Ideal.under ℤ P := by
    rw [Ideal.span_le]
    intro x hx
    have hx' : x = (ell : ℤ) := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    rw [Ideal.under_def]
    change algebraMap ℤ (𝓞 K) (ell : ℤ) ∈ P
    simpa only [map_natCast] using hP
  have hp_le_Q : p ≤ Ideal.under ℤ Q := by
    rw [Ideal.span_le]
    intro x hx
    have hx' : x = (ell : ℤ) := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    rw [Ideal.under_def]
    change algebraMap ℤ (𝓞 K) (ell : ℤ) ∈ Q
    simpa only [map_natCast] using hQ
  have hPunder_prime : (Ideal.under ℤ P).IsPrime := hPprime.under ℤ P
  have hQunder_prime : (Ideal.under ℤ Q).IsPrime := hQprime.under ℤ Q
  have hp_eq_P : p = Ideal.under ℤ P := hpmax.eq_of_le hPunder_prime.ne_top hp_le_P
  have hp_eq_Q : p = Ideal.under ℤ Q := hpmax.eq_of_le hQunder_prime.ne_top hp_le_Q
  have : P.LiesOver p := (Ideal.liesOver_iff P p).2 hp_eq_P
  have : Q.LiesOver p := (Ideal.liesOver_iff Q p).2 hp_eq_Q
  obtain ⟨τ, hτ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup p P Q (G := K ≃ₐ[ℚ] K)
  refine ⟨τ, ?_⟩
  rw [← Catalan.ideal_pointwise_smul_eq_map K τ P]
  exact hτ

/-- 若 `γ` 乘上某元素等于单位乘 `ell ^ k`，且某极大理想 `Q` 不是 `P` 的任何 Galois 共轭，
则 `Q` 处的重数为零。 -/
theorem emultiplicity_eq_zero_of_not_conj
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (ell k : ℕ) (hell : ell.Prime)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (ell : 𝓞 K) ∈ P)
    {γ γ' u : 𝓞 K} (hu : IsUnit u) (hprod : γ * γ' = u * (ell : 𝓞 K) ^ k)
    (Q : Ideal (𝓞 K)) [Q.IsMaximal]
    (hne : ∀ τ : K ≃ₐ[ℚ] K, Ideal.map (Catalan.integerAut K τ).toRingHom P ≠ Q) :
    emultiplicity Q (Ideal.span {γ}) = 0 := by
  have hQprime : Q.IsPrime := Ideal.IsMaximal.isPrime (inferInstance : Q.IsMaximal)
  rw [emultiplicity_eq_zero]
  intro hdvd
  have hγQ : γ ∈ Q := by
    obtain ⟨X, hX⟩ := hdvd
    have hle : Ideal.span {γ} ≤ Q := by
      rw [hX]
      exact Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self γ)
  have hprodmem : u * (ell : 𝓞 K) ^ k ∈ Q :=
    hprod ▸ Ideal.mul_mem_right _ _ hγQ
  have hupow : (ell : 𝓞 K) ^ k ∈ Q := by
    obtain ⟨v, hv⟩ := hu
    have hmem : (v⁻¹ : (𝓞 K)ˣ) * (u * (ell : 𝓞 K) ^ k) ∈ Q :=
      Ideal.mul_mem_left _ _ hprodmem
    rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at hmem
  have hellQ : (ell : 𝓞 K) ∈ Q := hQprime.mem_of_pow_mem k hupow
  obtain ⟨τ, hτ⟩ :=
    exists_integerAut_map_eq_of_natCast_mem K ell hell P Q hP hellQ
  exact hne τ hτ

end Catalan.Stickelberger
