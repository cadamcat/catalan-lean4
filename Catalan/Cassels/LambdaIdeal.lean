import Catalan.Cyclotomic.Basic
import Catalan.Cassels.Factorization

open NumberField
noncomputable section
namespace Catalan

/-- If p divides x−1, the normalized cyclotomic factor is integral and coprime to p. -/
lemma lambda_integral_coprime_of_prime_dvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ℤ) (hpx : (p : ℤ) ∣ x - 1)
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [Fact p.Prime] :
    ∃ l : 𝓞 K, (l : K) = ((x : K) - ζ p K) / (1 - ζ p K) ∧
      IsCoprime (p : 𝓞 K) l := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let η : 𝓞 K := (ζ_spec p K).toInteger
  let π : 𝓞 K := η - 1
  have hπ : Prime π := (ζ_spec p K).zeta_sub_one_prime'
  have hass : Associated (π ^ (p - 1)) (p : 𝓞 K) :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p (ζ_spec p K)
  have hπsq : π ^ 2 ∣ (p : 𝓞 K) :=
    (pow_dvd_pow π (by have := hp.two_le; omega)).trans hass.dvd
  have hpx' : (p : 𝓞 K) ∣ (x : 𝓞 K) - 1 := by
    simpa using (map_dvd (Int.castRingHom (𝓞 K)) hpx)
  obtain ⟨t, ht⟩ := hπsq.trans hpx'
  let l : 𝓞 K := 1 - π * t
  have hl : (1 - η) * l = (x : 𝓞 K) - η := by
    dsimp [l, π] at *
    linear_combination -ht
  refine ⟨l, ?_, ?_⟩
  · apply (eq_div_iff (sub_ne_zero.mpr ((ζ_spec p K).ne_one hp.one_lt).symm)).2
    have hc : (1 - ζ p K) * (l : K) = (x : K) - ζ p K := by
      have hc := congrArg (fun a : 𝓞 K => (a : K)) hl
      change (1 - ζ p K) * (l : K) = (x : K) - ζ p K at hc
      exact hc
    simpa [mul_comm] using hc
  · apply IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd p (ζ_spec p K)
    intro hd
    have h1 : π ∣ (1 : 𝓞 K) := by
      convert dvd_add hd (dvd_mul_right π t) using 1
      dsimp [l]
      ring
    exact hπ.not_isUnit (isUnit_of_dvd_one h1)


/-- A coprime normalized root factor in a Dedekind domain generates a q-th-power ideal. -/
lemma ideal_pow_of_root_factor {A : Type*} [CommRing A] [IsDedekindDomain A] (p q : ℕ) (η x y l : A)
    (hη : IsPrimitiveRoot η p) (hp : 0 < p)
    (hl : (1 - η) * l = x - η) (hlp : IsCoprime (p : A) l)
    (hπη : 1 - η ∣ (p : A)) (h : x ^ p = y ^ q + 1) :
    ∃ a : Ideal A, Ideal.span {l} = a ^ q := by
  classical
  let B : A := ∑ i ∈ Finset.range p, x ^ i * η ^ (p - 1 - i)
  have hηunit : IsUnit η := hη.isUnit hp.ne'
  have hdiff : x - η ∣ B - (p : A) * η ^ (p - 1) := by
    rw [← geom_sum₂_self η p]
    dsimp [B]
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i hi
    rw [← sub_mul]
    exact dvd_mul_of_dvd_left (sub_dvd_pow_sub_pow x η i) _
  have hldiff : l ∣ B - (p : A) * η ^ (p - 1) := by
    apply dvd_trans _ hdiff
    rw [← hl]
    exact dvd_mul_left l (1 - η)
  have hlpη : IsCoprime l ((p : A) * η ^ (p - 1)) :=
    (isCoprime_mul_unit_right_right (hηunit.pow _) _ _).mpr hlp.symm
  obtain ⟨d, hd⟩ := hldiff
  have hlB : IsCoprime l B := by
    have heq : B = (p : A) * η ^ (p - 1) + l * d := by linear_combination hd
    rw [heq]
    exact hlpη.add_mul_left_right d
  have hlπ : IsCoprime l (1 - η) := hlp.symm.of_isCoprime_of_dvd_right hπη
  have hprod : l * ((1 - η) * B) = y ^ q := by
    calc
      l * ((1 - η) * B) = B * (x - η) := by rw [← hl]; ring
      _ = x ^ p - η ^ p := geom_sum₂_mul x η p
      _ = y ^ q := by rw [hη.pow_eq_one, h]; ring
  have hc : IsCoprime (Ideal.span {l}) (Ideal.span {(1 - η) * B}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (hlπ.mul_right hlB)
  have hg : IsUnit (gcd (Ideal.span {l}) (Ideal.span {(1 - η) * B})) := by
    rw [Ideal.isCoprime_iff_gcd.mp hc]
    exact isUnit_one
  apply exists_eq_pow_of_mul_eq_pow hg (c := Ideal.span {y})
  simp only [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow, hprod]


/-- Bilu Proposition 5.2: the normalized cyclotomic factor generates a q-th-power ideal. -/
theorem lambda_ideal_pow (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [Fact p.Prime] :
    ∃ (l : 𝓞 K) (𝔞 : Ideal (𝓞 K)),
      (l : K) = ((x : K) - ζ p K) / (1 - ζ p K) ∧ Ideal.span {l} = 𝔞 ^ q := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, b, u, v, ha, hb, hu, hv, hxa, hrest⟩ :=
    cassels_factorization p q hp hq hp2 hq2 x y hx hy h
  have hpx : (p : ℤ) ∣ x - 1 := by
    rw [hxa]
    apply dvd_mul_of_dvd_left
    exact dvd_pow_self _ (by have := hq.two_le; omega)
  obtain ⟨l, hl, hlp⟩ := lambda_integral_coprime_of_prime_dvd p hp hp2 x hpx K
  let η : 𝓞 K := (ζ_spec p K).toInteger
  have hη : IsPrimitiveRoot η p := (ζ_spec p K).toInteger_isPrimitiveRoot
  have hrel : (1 - η) * l = (x : 𝓞 K) - η := by
    apply RingOfIntegers.coe_injective
    change (1 - ζ p K) * (l : K) = (x : K) - ζ p K
    rw [hl, mul_div_cancel₀ _ (sub_ne_zero.mpr ((ζ_spec p K).ne_one hp.one_lt).symm)]
  have hπη : 1 - η ∣ (p : 𝓞 K) := by
    simpa only [neg_sub] using ((ζ_spec p K).toInteger_sub_one_dvd_prime').neg_left
  have heq : (x : 𝓞 K) ^ p = (y : 𝓞 K) ^ q + 1 := by
    simpa using congrArg (Int.castRingHom (𝓞 K)) h
  obtain ⟨𝔞, h𝔞⟩ := ideal_pow_of_root_factor p q η (x : 𝓞 K) (y : 𝓞 K) l
    hη hp.pos hrel hlp hπη heq
  exact ⟨l, 𝔞, hl, h𝔞⟩

end Catalan
