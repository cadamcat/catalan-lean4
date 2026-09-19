import Catalan.Mihailescu.PrimeOrder

/-! Separation of the conjugate factors x−σ(ζ) by integer-valued orders. -/
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance separationDecidableEqG : DecidableEq (G p K) := Classical.decEq _

lemma coe_actUnit_xmζ (hp2 : p ≠ 2) (x : ℤ) (s : G p K) :
    (actUnit p K s (xmζ p K x hp2) : K) =
      ((x : 𝓞 K) - zetaConjInt p K s : 𝓞 K) := by
  change s ((x : K) - ζ p K) = (x : K) - s (ζ p K)
  simp only [map_sub, map_intCast]

lemma other_prime_not_mem_conjugate (hp2 : p ≠ 2) (x : ℤ)
    (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q.asIdeal ≠ ramifiedPrime p K)
    (hxQ : (x : 𝓞 K) - zetaConjInt p K 1 ∈ Q.asIdeal)
    (s : G p K) (hs : s ≠ 1) :
    (x : 𝓞 K) - zetaConjInt p K s ∉ Q.asIdeal := by
  intro hxs
  have hle : ramifiedPrime p K ≤ Q.asIdeal := by
    apply (eq10 p K hp2 x 1 s hs.symm).trans
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxQ
    · exact hxs
  have hf := ramifiedPrime_facts p K hp2
  exact hQP ((hf.1.isMaximal hf.2.1).eq_of_le Q.isPrime.ne_top hle).symm

lemma exists_separating_orders (hp2 : p ≠ 2) (x : ℤ)
    (hx : 2 ≤ |x|) (hexc : p = 3 → x ≠ -2) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ ∃ v : G p K → (Kˣ →* Multiplicative ℤ),
      ∀ s t : G p K,
        (v s (actUnit p K t (xmζ p K x hp2))).toAdd = if s = t then ℓ else 0 := by
  classical
  obtain ⟨Q, hQ, hQ0, hQP, hxQ⟩ := exists_other_prime_divisor p K hp2 x hx hexc
  let P : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, hQ0⟩
  let w := primeOrder K P
  let u := xmζ p K x hp2
  let ℓ : ℤ := (w u).toAdd
  have hupos : 0 < ℓ := by
    apply (primeOrder_integral_pos_iff K P u ((x : 𝓞 K) - zetaConjInt p K 1) ?_).mpr hxQ
    change (x : K) - ζ p K = (x : K) - ζ p K
    rfl
  let v : G p K → (Kˣ →* Multiplicative ℤ) := fun s => w.comp (actUnit p K s⁻¹)
  refine ⟨ℓ, hupos, v, ?_⟩
  intro s t
  change (w (actUnit p K s⁻¹ (actUnit p K t u))).toAdd = _
  rw [← actUnit_mul]
  by_cases hst : s = t
  · subst t
    rw [inv_mul_cancel, if_pos rfl]
    rfl
  · rw [if_neg hst]
    have hne : s⁻¹ * t ≠ 1 := by
      intro h
      exact hst (inv_mul_eq_one.mp h)
    exact primeOrder_integral_eq_zero K P _
      ((x : 𝓞 K) - zetaConjInt p K (s⁻¹ * t))
      (coe_actUnit_xmζ p K hp2 x (s⁻¹ * t))
      (other_prime_not_mem_conjugate p K hp2 x P hQP hxQ (s⁻¹ * t) hne)

local instance separationFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma upow_eq_one_iff (hp2 : p ≠ 2) (x : ℤ)
    (hx : 2 ≤ |x|) (hexc : p = 3 → x ≠ -2) (Θ : R p K) :
    upow p K (xmζ p K x hp2) Θ = 1 ↔ Θ = 0 := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓ, v, hv⟩ := exists_separating_orders p K hp2 x hx hexc
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro σ
    have hc := order_upow p K (v σ) (xmζ p K x hp2) Θ
    rw [h, map_one] at hc
    have hsum : (∑ τ : G p K, Θ.coeff τ *
        (v σ (actUnit p K τ (xmζ p K x hp2))).toAdd) = Θ.coeff σ * ℓ := by
      simp only [hv, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hsum] at hc
    have hmul : Θ.coeff σ * ℓ = 0 := hc.symm
    have hz := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hℓ)
    simpa only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hz
  · rintro rfl
    exact upow_zero p K _

variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma alpha_ne_one (hp2 : p ≠ 2) (hx : 2 ≤ |x|)
    (hexc : p = 3 → x ≠ -2) (Θ : mihIdeal p K q x hp2) (hΘ : Θ.val ≠ 0) :
    alpha p K q x hp2 Θ ≠ 1 := by
  intro ha
  have h := alpha_pow p K q x hp2 Θ
  rw [ha, one_pow] at h
  exact hΘ ((upow_eq_one_iff p K hp2 x hx hexc Θ.val).mp h.symm)

end Catalan
