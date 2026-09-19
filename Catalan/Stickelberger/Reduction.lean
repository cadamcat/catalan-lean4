import Catalan.IdealHelpers
import Catalan.Stickelberger.ClassReduction

/-! Algebraic reduction of Stickelberger annihilation to generator witnesses.
The required witnesses remain explicit premises; this is not the final theorem. -/
open scoped BigOperators nonZeroDivisors Pointwise
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma ΘS_zero : ΘS p K 0 = 0 := by
  simp only [ΘS, Nat.mul_zero, Nat.zero_div, Nat.cast_zero,
    MonoidAlgebra.single_zero, Finset.sum_const_zero]

lemma ΘS_p : ΘS p K p = pθ p K := by
  simp only [ΘS, pθ, Nat.mul_div_cancel _ hp.out.pos]

lemma ΘS_mod_decomposition (k : ℕ) :
    ΘS p K k = ((k / p : ℕ) : ℤ) • pθ p K + ΘS p K (k % p) := by
  classical
  have hdiv (a : ℕ) : a * k / p = (k / p) * a + a * (k % p) / p := by
    calc
      a * k / p = (a * (k % p) + p * (a * (k / p))) / p := by
        congr 1
        calc
          a * k = a * (k % p + p * (k / p)) :=
            congrArg (fun t : ℕ => a * t) (Nat.mod_add_div k p).symm
          _ = a * (k % p) + p * (a * (k / p)) := by ring
      _ = a * (k % p) / p + a * (k / p) :=
        Nat.add_mul_div_left _ _ hp.out.pos
      _ = (k / p) * a + a * (k % p) / p := by ac_rfl
  unfold ΘS pθ
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MonoidAlgebra.smul_single, ← MonoidAlgebra.single_add]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_mul, smul_eq_mul] using
    congrArg (fun n : ℕ => (n : ℤ)) (hdiv (a : ZMod p).val)

theorem stickelberger_from_generators
    (hgen : ∀ (k : ℕ), 0 < k → k ≤ p → ∀ J : FracIdealUnit K,
      ∃ γ : Kˣ, ipow p K J (ΘS p K k) = principalIdeal K γ)
    (Θ : R p K) (hΘ : Θ ∈ stickSpan p K) (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  let S : Submodule ℤ (R p K) := principalExponentSubmodule p K J
  have hpθ : pθ p K ∈ S := by
    rw [← ΘS_p p K]
    exact hgen p hp.out.pos le_rfl J
  have hsmall (r : ℕ) (hr : r < p) : ΘS p K r ∈ S := by
    by_cases hr0 : r = 0
    · rw [hr0, ΘS_zero]
      exact S.zero_mem
    · exact hgen r (Nat.pos_of_ne_zero hr0) hr.le J
  have hall (k : ℕ) : ΘS p K k ∈ S := by
    rw [ΘS_mod_decomposition]
    exact S.add_mem (S.smul_mem ((k / p : ℕ) : ℤ) hpθ)
      (hsmall (k % p) (Nat.mod_lt k hp.out.pos))
  have hle : stickSpan p K ≤ S := by
    apply Submodule.span_le.mpr
    intro A hA
    rcases hA with hA | hA
    · obtain ⟨k, rfl⟩ := hA
      exact hall k
    · have hA' : A = pθ p K := Set.mem_singleton_iff.mp hA
      rw [hA']
      exact hpθ
  exact hle hΘ


/-- The remaining away-prime witnesses suffice for every exponent in the span. -/
theorem stickelberger_from_away_generators
    (haway : ∀ (I : Ideal (𝓞 K)) (hI : I.IsPrime) (hI0 : I ≠ ⊥),
      (p : 𝓞 K) ∉ I → ∀ (k : ℕ), 0 < k → k ≤ p →
        ∃ γ : Kˣ, ipow p K (idealUnit K I hI0) (ΘS p K k) = principalIdeal K γ)
    (Θ : R p K) (hΘ : Θ ∈ stickSpan p K) (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  apply stickelberger_from_generators p K ?_ Θ hΘ J
  intro k hk0 hkp J
  refine fractionalIdeal_prime_induction K
    (fun J => ∃ γ : Kˣ, ipow p K J (ΘS p K k) = principalIdeal K γ)
    ?_ ?_ ?_ ?_ J
  · exact ⟨1, by rw [ipow_one, map_one]⟩
  · rintro I J ⟨α, hα⟩ ⟨β, hβ⟩
    exact ⟨α * β, by rw [ipow_mul, hα, hβ, map_mul]⟩
  · rintro I ⟨α, hα⟩
    exact ⟨α⁻¹, by rw [ipow_inv, hα, map_inv]⟩
  · intro I hI hI0
    by_cases hpI : (p : 𝓞 K) ∈ I
    · obtain ⟨δ, hδ⟩ := prime_over_p_principal p K I hI hI0 hpI
      refine ⟨(ΘS p K k).coeff.prod (fun τ n => (elementAct K τ δ) ^ n), ?_⟩
      rw [hδ, ipow_principalIdeal]
    · exact haway I hI hI0 hpI k hk0 hkp

/-- It suffices to construct generator witnesses for primes outside 2p.
The class-representative reduction handles primes above 2 and p. -/
theorem stickelberger_from_primes_away_two_mul
    (hgen : ∀ (I : Ideal (𝓞 K)) (_hI : I.IsPrime) (hI0 : I ≠ ⊥),
      (2 * p : 𝓞 K) ∉ I → ∀ (k : ℕ), 0 < k → k ≤ p →
        ∃ γ : Kˣ, ipow p K (idealUnit K I hI0) (ΘS p K k) = principalIdeal K γ)
    (Θ : R p K) (hΘ : Θ ∈ stickSpan p K) (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  apply stickelberger_from_generators p K ?_ Θ hΘ J
  intro k hk0 hkp J
  exact fractional_generator_of_primes_away_two_mul p hp.out.ne_zero K (ΘS p K k)
    (fun I hI hI0 hIaway => hgen I hI hI0 hIaway k hk0 hkp) J

end Catalan
