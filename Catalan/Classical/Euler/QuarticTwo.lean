module

public import Mathlib

/-!
# `Catalan.Classical.Euler.QuarticTwo`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Euler

lemma quartic_pell_two (x y : ℤ) (h : x ^ 4 - 2 * y ^ 2 = 1) :
    (x = 1 ∨ x = -1) ∧ y = 0 := by
  have odd_not_even : ∀ z : ℤ, Odd z → Even z → False := by
    intro z ho he
    obtain ⟨a, ha⟩ := ho
    obtain ⟨b, hb⟩ := he
    omega
  have hxodd : Odd x := by
    by_contra hxo
    have hxe : Even x := (Int.even_or_odd x).resolve_right hxo
    have hx4even : Even (x ^ 4) := by
      have he := Even.mul_left hxe (x ^ 3)
      simpa only [← pow_succ] using he
    have hxp : x ^ 4 = 1 + 2 * y ^ 2 := by linarith
    have h2even : Even (2 * y ^ 2) := by
      exact Even.mul_right (show Even (2 : ℤ) by norm_num) (y ^ 2)
    have hx4odd : Odd (x ^ 4) := by
      rw [hxp]
      simpa only [add_comm] using h2even.add_one
    exact odd_not_even (x ^ 4) hx4odd hx4even
  obtain ⟨m, hm⟩ := hxodd
  let k : ℤ := m * (m + 1)
  have hk : 0 ≤ k := by
    dsimp [k]
    by_cases hm0 : 0 ≤ m
    · exact mul_nonneg hm0 (by omega)
    · have hmle : m ≤ 0 := by omega
      have hm1le : m + 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos hmle hm1le
  have hx2 : x ^ 2 = 1 + 4 * k := by
    dsimp [k]
    rw [hm]
    ring
  have hx4 : x ^ 4 = (1 + 4 * k) ^ 2 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]
  have hsq : (4 * k) * (2 * k + 1) = y ^ 2 := by
    nlinarith [h, hx4]
  have hgcd : (4 * k).gcd (2 * k + 1) = 1 := by
    rw [Int.gcd_eq_one_iff]
    intro c hc1 hc2
    have hc_two : c ∣ 2 := by
      have htmp := dvd_sub (dvd_mul_of_dvd_right hc2 2) hc1
      have htmp' : c ∣ (2 * (2 * k + 1) - 4 * k) := htmp
      convert htmp' using 1
      ring
    have htmp := dvd_sub hc2 (dvd_mul_of_dvd_right hc_two k)
    have htmp' : c ∣ ((2 * k + 1) - k * 2) := htmp
    convert htmp' using 1
    ring
  obtain ⟨a, ha | ha⟩ := Int.sq_of_gcd_eq_one hgcd hsq
  · have h4k : 4 * k = a ^ 2 := ha
    have hfac : (x - a) * (x + a) = 1 := by
      calc
        (x - a) * (x + a) = x ^ 2 - a ^ 2 := by ring
        _ = 1 := by rw [hx2, h4k]; ring
    rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hfac) with hpos | hneg
    ·
      have hxval : x = 1 := by linarith [hpos.1, hpos.2]
      refine ⟨Or.inl hxval, ?_⟩
      rw [hxval] at h
      nlinarith
      
    · 
      have hxval : x = -1 := by linarith [hneg.1, hneg.2]
      refine ⟨Or.inr hxval, ?_⟩
      rw [hxval] at h
      nlinarith
  · have h4k_nonneg : 0 ≤ 4 * k := by positivity
    have ha0 : a = 0 := by nlinarith [ha, sq_nonneg a]
    have h4k : 4 * k = a ^ 2 := by nlinarith [ha, ha0]
    have hfac : (x - a) * (x + a) = 1 := by
      calc
        (x - a) * (x + a) = x ^ 2 - a ^ 2 := by ring
        _ = 1 := by rw [hx2, h4k]; ring
    rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hfac) with hpos | hneg
    · 
      have hxval : x = 1 := by linarith [hpos.1, hpos.2]
      refine ⟨Or.inl hxval, ?_⟩
      rw [hxval] at h
      nlinarith
      
    · 
      have hxval : x = -1 := by linarith [hneg.1, hneg.2]
      refine ⟨Or.inr hxval, ?_⟩
      rw [hxval] at h
      nlinarith

end Catalan.Euler
