import Catalan.Runge.Definitions

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

lemma binomRat_nat_div_eq_casselsCoeff (n q k : ℕ) (hq : q ≠ 0) :
    binomRat ((n : ℚ) / (q : ℚ)) k = casselsCoeff n q k := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hfactor (j : ℕ) : (n : ℚ) / (q : ℚ) - (j : ℚ) =
      ((n : ℚ) - (j : ℚ) * (q : ℚ)) / (q : ℚ) := by
    field_simp [hqQ]
  unfold binomRat casselsCoeff
  simp_rw [hfactor]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, div_div]

lemma D_sum_le (q : ℕ) (hq : q.Prime) (α : Type*) [Fintype α] (f : α → ℕ) :
    (∑ i : α, D q (f i)) ≤ D q (∑ i : α, f i) := by
  classical
  let instPrimeQ : Fact q.Prime := ⟨hq⟩
  have hdiv : q ^ (∑ i : α, padicValNat q (f i).factorial) ∣
      (∑ i : α, f i).factorial := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_padicValNat_dvd).trans
      (Nat.prod_factorial_dvd_factorial_sum Finset.univ f)
  have hv : (∑ i : α, padicValNat q (f i).factorial) ≤
      padicValNat q (∑ i : α, f i).factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp hdiv
  simpa only [D, casselsDenExp, Finset.sum_add_distrib] using
    Nat.add_le_add_left hv (∑ i : α, f i)


section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance coefficientIntegralGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma runge_coeff_integral (q : ℕ) (hq : q.Prime) (Theta : R p K)
    (hn : ∀ g, 0 ≤ Theta.coeff g) (k : ℕ) :
    (∃ a : 𝓞 K, ∃ j : ℕ, (q : K) ^ j * rungeCoeff p K q Theta k = (a : K)) ∧
    IsIntegral ℤ ((q : K) ^ D q k * rungeCoeff p K q Theta k) := by
  classical
  have hqK : (q : K) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hscaled (g : G p K) (j : ℕ) : IsIntegral ℤ
      ((q : K) ^ D q j *
        algebraMap ℚ K (binomRat ((Theta.coeff g : ℚ) / (q : ℚ)) j)) := by
    obtain ⟨n, hncast⟩ := Int.eq_ofNat_of_zero_le (hn g)
    rw [hncast, Int.cast_natCast,
      binomRat_nat_div_eq_casselsCoeff n q j hq.ne_zero,
      cassels_coeff_eq_coeffNum n q j hq]
    simp only [map_div₀, map_intCast, map_pow, map_natCast, D]
    convert (isIntegral_intCast (R := ℤ) (B := K) (casselsCoeffNum n q j)) using 1
    field_simp [hqK]
  have hint : IsIntegral ℤ ((q : K) ^ D q k * rungeCoeff p K q Theta k) := by
    rw [rungeCoeff, Finset.mul_sum]
    apply IsIntegral.sum
    intro f _
    by_cases hf : (∑ g : G p K, (f g).val) = k
    · rw [if_pos hf]
      have hprod : IsIntegral ℤ
          ((q : K) ^ (∑ g : G p K, D q (f g).val) *
            ∏ g : G p K,
              (algebraMap ℚ K (binomRat ((Theta.coeff g : ℚ) / (q : ℚ)) (f g).val) *
                (-g (ζ p K)) ^ (f g).val)) := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        apply IsIntegral.prod
        intro g _
        rw [← mul_assoc]
        exact (hscaled g (f g).val).mul (((integral_conj_zeta p K g).neg).pow _)
      have hle : (∑ g : G p K, D q (f g).val) ≤ D q k := by
        simpa only [hf] using D_sum_le q hq (G p K) (fun g => (f g).val)
      have hnat : IsIntegral ℤ (q : K) := isIntegral_natCast q
      convert (hnat.pow (D q k - ∑ g : G p K, D q (f g).val)).mul hprod using 1
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · rw [if_neg hf, mul_zero]
      exact isIntegral_zero
  exact ⟨⟨⟨_, hint⟩, D q k, rfl⟩, hint⟩

end Cyclotomic
end Catalan.Runge
