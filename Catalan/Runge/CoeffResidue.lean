import Catalan.Runge.Definitions
import Catalan.Runge.ProductCoefficients

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge
open scoped Classical

private lemma sum_pow_bounded
    {ι R : Type*} [Fintype ι] [CommSemiring R] (x : ι → R) (k : ℕ) :
    (∑ i, x i) ^ k =
      ∑ f : ι → Fin (k + 1), if (∑ i, (f i).val) = k then
        (Nat.multinomial Finset.univ (fun i => (f i).val) : R) * ∏ i, x i ^ (f i).val
      else 0 := by
  classical
  rw [sum_bounded_eq_piAntidiag k
    (fun f : ι → ℕ => (Nat.multinomial Finset.univ f : R) * ∏ i, x i ^ f i)]
  exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ x k

private lemma scaled_binomRat (q : ℕ) (hq : q ≠ 0) (n : ℤ) (i : ℕ) :
    (q : ℚ) ^ i * (Nat.factorial i : ℚ) * binomRat ((n : ℚ) / q) i =
      ∏ j ∈ Finset.range i, ((n : ℚ) - (j : ℚ) * q) := by
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hfac : (Nat.factorial i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  calc
    _ = (q : ℚ) ^ i * ∏ j ∈ Finset.range i, ((n : ℚ) / q - j) := by
      unfold binomRat
      field_simp
    _ = ∏ j ∈ Finset.range i, ((q : ℚ) * ((n : ℚ) / q - j)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      field_simp

private lemma scaled_binomRat_map (K : Type*) [Field K] [CharZero K]
    (q : ℕ) (hq : q ≠ 0) (n : ℤ) (i : ℕ) :
    (q : K) ^ i * (Nat.factorial i : K) *
      algebraMap ℚ K (binomRat ((n : ℚ) / q) i) =
      ∏ j ∈ Finset.range i, ((n : K) - (j : K) * q) := by
  simpa only [map_mul, map_pow, map_natCast, map_intCast, map_prod, map_sub] using
    congrArg (algebraMap ℚ K) (scaled_binomRat q hq n i)

private lemma scaled_product
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (q : ℕ) (hq : q ≠ 0) (n : ι → ℤ) (z : ι → K) (m : ι → ℕ) (k : ℕ)
    (hsum : ∑ i, m i = k) :
    (q : K) ^ k * (Nat.factorial k : K) *
        (∏ i, algebraMap ℚ K (binomRat ((n i : ℚ) / q) (m i)) * z i ^ m i) =
      (Nat.multinomial Finset.univ m : K) *
        ∏ i, (∏ j ∈ Finset.range (m i), ((n i : K) - (j : K) * q)) * z i ^ m i := by
  have hfac : (Nat.factorial k : K) =
      (∏ i, (Nat.factorial (m i) : K)) * (Nat.multinomial Finset.univ m : K) := by
    rw [← hsum]
    exact_mod_cast (Nat.multinomial_spec Finset.univ m).symm
  have hpow : (q : K) ^ k = ∏ i, (q : K) ^ m i := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [hpow, hfac]
  calc
    _ = (Nat.multinomial Finset.univ m : K) *
        ∏ i, ((q : K) ^ m i * (Nat.factorial (m i) : K) *
          (algebraMap ℚ K (binomRat ((n i : ℚ) / q) (m i)) * z i ^ m i)) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [← mul_assoc, scaled_binomRat_map K q hq (n i) (m i)]

private lemma weighted_falling_sum_mod
    {ι R : Type*} [Fintype ι] [CommRing R]
    (q : ℕ) (n : ι → ℤ) (z : ι → R) (k : ℕ) :
    (q : R) ∣
      (∑ f : ι → Fin (k + 1), if (∑ i, (f i).val) = k then
        (Nat.multinomial Finset.univ (fun i => (f i).val) : R) *
          ∏ i, (∏ j ∈ Finset.range (f i).val, ((n i : R) - (j : R) * q)) *
            z i ^ (f i).val
        else 0) - (∑ i, (n i : R) * z i) ^ k := by
  let I : Ideal R := Ideal.span {(q : R)}
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hq0 : (q : R ⧸ I) = 0 := by
    have h := (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr
      (Ideal.mem_span_singleton_self (q : R))
    simpa only [map_natCast] using h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq (I := I)).mp
  have h := (sum_pow_bounded (fun i => π (n i : R) * π (z i)) k).symm
  simpa only [map_sum, apply_ite, map_zero, map_natCast, map_intCast, map_mul,
    map_prod, map_sub, map_pow, hq0, mul_zero, sub_zero, Finset.prod_const,
    Finset.card_range, mul_pow] using h


section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance coeffResidueGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma runge_coeff_residue (q : ℕ) (hq : q.Prime) (Theta : R p K)
    (hn : ∀ g, 0 ≤ Theta.coeff g) (k : ℕ) :
    ∃ w : 𝓞 K,
      (q : K) ^ k * (Nat.factorial k : K) * rungeCoeff p K q Theta k -
        (-(∑ g : G p K, (Theta.coeff g : K) * g (ζ p K))) ^ k = (q : K) * (w : K) := by
  let z : G p K → 𝓞 K := fun g =>
    -RingOfIntegers.mapRingHom g.toRingHom (ζ_spec p K).toInteger
  have hz (g : G p K) : ((z g : 𝓞 K) : K) = -g (ζ p K) := rfl
  let A : 𝓞 K := ∑ f : G p K → Fin (k + 1),
    if (∑ g : G p K, (f g).val) = k then
      (Nat.multinomial Finset.univ (fun g => (f g).val) : 𝓞 K) *
        ∏ g : G p K,
          (∏ j ∈ Finset.range (f g).val, ((Theta.coeff g : 𝓞 K) - (j : 𝓞 K) * q)) *
            z g ^ (f g).val
    else 0
  have hA : (q : K) ^ k * (Nat.factorial k : K) * rungeCoeff p K q Theta k = (A : K) := by
    unfold rungeCoeff
    rw [Finset.mul_sum]
    change _ = algebraMap (𝓞 K) K A
    simp only [A, map_sum, apply_ite, map_zero, map_natCast, map_intCast, map_mul,
      map_prod, map_sub, map_pow, hz]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hs : (∑ g : G p K, (f g).val) = k
    · simp only [if_pos hs]
      exact scaled_product q hq.ne_zero (fun g => Theta.coeff g)
        (fun g => -g (ζ p K)) (fun g => (f g).val) k hs
    · simp only [if_neg hs, mul_zero]
  have hdiv : (q : 𝓞 K) ∣ A - (∑ g : G p K, (Theta.coeff g : 𝓞 K) * z g) ^ k :=
    weighted_falling_sum_mod q (fun g => Theta.coeff g) z k
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w, ?_⟩
  rw [hA]
  have hsum : ((∑ g : G p K, (Theta.coeff g : 𝓞 K) * z g : 𝓞 K) : K) =
      -(∑ g : G p K, (Theta.coeff g : K) * g (ζ p K)) := by
    change algebraMap (𝓞 K) K _ = _
    simp only [map_sum, map_mul, map_intCast, hz, mul_neg, Finset.sum_neg_distrib]
  rw [← hsum]
  simpa only [map_sub, map_pow, map_mul, map_natCast] using
    congrArg (algebraMap (𝓞 K) K) hw

end Cyclotomic
end Catalan.Runge
