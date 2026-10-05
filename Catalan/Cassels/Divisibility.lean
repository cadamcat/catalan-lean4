module

public import Catalan.Cassels.EasyDivisibility
public import Catalan.Cassels.Relations
public import Catalan.Cassels.LowerBound
public import Catalan.Cassels.ErrorBound
public import Catalan.Cassels.ErrorIntegral

/-!
# `Catalan.Cassels.Divisibility`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma cassels_lower_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (hqx : (q : ℤ) ∣ x) :
    (q : ℤ) ^ (p - 1) + q ≤ |x| := by
  obtain ⟨b, u, hb, hu, hyb, hsu, hxu⟩ :=
    cassels_partial_q_relations p q hp hq hp2 hq2 x y hx hy h hqx
  exact cassels_lower_bound_from_relations p q hp hq hp2 hq2 hqp
    x y b u hb hu hyb hsu hxu

lemma cassels_scaled_error_small (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (x y a : ℤ) (ha : 2 ≤ |a|) (hxa : x - 1 = a ^ q)
    (h : x ^ p = y ^ q + 1)
    (hlarge : (q : ℤ) ^ (p - 1) + q ≤ |x|) :
    |(casselsScale p q : ℚ) * casselsError p q a y| < 1 := by
  have hq3N : 3 ≤ q := by have ht := hq.two_le; omega
  have hq3 : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3N
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqpos
  have hQpos : (0 : ℚ) < (q : ℚ) ^ (p - 1) := pow_pos hqpos _
  have hlargeQ : (q : ℚ) ^ (p - 1) + (q : ℚ) ≤ ((|x| : ℤ) : ℚ) := by
    exact_mod_cast hlarge
  have hden : (q : ℚ) ^ (p - 1) ≤ ((|x| : ℤ) : ℚ) - 3 := by linarith
  have herr := cassels_error_bound p q hp hq hp2 hq2 hqp x y a ha hxa h
  have herr' : |casselsError p q a y| ≤ 1 / (q : ℚ) ^ (p - 1) :=
    le_trans herr (one_div_le_one_div_of_le hQpos hden)
  have hE := cassels_denexp_bound p q hp hq hp2 hq2 hqp
  let E := casselsDenExp q (casselsIndex p q)
  have hscale : (casselsScale p q : ℚ) = (q : ℚ) ^ E := by
    simp only [casselsScale, Int.cast_pow, Int.cast_natCast, E]
  have hDpos : (0 : ℚ) ≤ (casselsScale p q : ℚ) := by
    rw [hscale]
    exact pow_nonneg hqpos.le _
  have hDle : (casselsScale p q : ℚ) ≤ (q : ℚ) ^ (p - 2) := by
    rw [hscale]
    have he : E + (p - 2 - E) = p - 2 := by dsimp [E]; omega
    have hone : (1 : ℚ) ≤ (q : ℚ) ^ (p - 2 - E) := by
      have hbase : (1 : ℚ) ≤ (q : ℚ) := by linarith
      induction (p - 2 - E) with
      | zero => simp only [pow_zero, le_refl]
      | succ n ih =>
          rw [pow_succ]
          have hm := mul_le_mul_of_nonneg_right ih hqpos.le
          nlinarith
    have ht := mul_le_mul_of_nonneg_left hone (pow_nonneg hqpos.le E)
    rw [mul_one, ← pow_add, he] at ht
    exact ht
  calc
    |(casselsScale p q : ℚ) * casselsError p q a y| =
        (casselsScale p q : ℚ) * |casselsError p q a y| := by
          rw [abs_mul, abs_of_nonneg hDpos]
    _ ≤ (q : ℚ) ^ (p - 2) * (1 / (q : ℚ) ^ (p - 1)) :=
      mul_le_mul hDle herr' (abs_nonneg _) (pow_nonneg hqpos.le _)
    _ = 1 / (q : ℚ) := by
      have he : p - 1 = (p - 2) + 1 := by have ht := hp.two_le; omega
      rw [he, pow_succ]
      field_simp [hq0] <;> ring
    _ ≤ (1 : ℚ) / 3 := one_div_le_one_div_of_le (by norm_num) hq3
    _ < 1 := by norm_num

lemma cassels_ordered_p_dvd_y (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (p : ℤ) ∣ y := by
  by_contra hpy
  have hqx := cassels_easy_q_dvd_x p q hp hq hp2 hq2 hqp x y hx hy h
  have hlarge := cassels_lower_bound p q hp hq hp2 hq2 hqp x y hx hy h hqx
  obtain ⟨a, ha0, hxa⟩ := cassels_bad_factor p q hp hq hq2 x y hy h hpy
  have hoq : Odd q := hq.odd_of_ne_two hq2
  have ha1 : a ≠ 1 := by
    intro ha
    rw [ha, one_pow] at hxa
    have hx2 : x = 2 := by linarith
    have hqdiv2 : q ∣ 2 := by
      rw [hx2] at hqx
      exact_mod_cast hqx
    rcases (Nat.dvd_prime Nat.prime_two).mp hqdiv2 with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq2 hqeq
  have ham1 : a ≠ -1 := by
    intro ha
    rw [ha, hoq.neg_pow, one_pow] at hxa
    exact hx (by linarith)
  have ha : 2 ≤ |a| := by
    by_contra hn
    have hab : |a| < 2 := by omega
    have ht := abs_lt.mp hab
    omega
  have hqnp : ¬ q ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with hq1 | hqeq
    · exact hq.ne_one hq1
    · omega
  obtain ⟨N, hN0, hN⟩ := cassels_error_integral_nonzero p q hq hqnp a y
  have hsmall := cassels_scaled_error_small p q hp hq hp2 hq2 hqp
    x y a ha hxa h hlarge
  rw [← hN] at hsmall
  have hNZ : |N| < (1 : ℤ) := by exact_mod_cast hsmall
  have ht := abs_lt.mp hNZ
  exact hN0 (by omega)

theorem cassels_p_dvd_y (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (p : ℤ) ∣ y := by
  rcases lt_trichotomy q p with hqp | hqp | hpq
  · exact cassels_ordered_p_dvd_y p q hp hq hp2 hq2 hqp x y hx hy h
  · subst q
    exact (cassels_equal_exponents_false p hp hp2 x y hx hy h).elim
  · have hs := cassels_solution_symm p q (hp.odd_of_ne_two hp2)
      (hq.odd_of_ne_two hq2) x y h
    have hd := cassels_easy_q_dvd_x q p hq hp hq2 hp2 hpq
      (-y) (-x) (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hs
    simpa only [dvd_neg] using hd

theorem cassels_q_dvd_x (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (q : ℤ) ∣ x := by
  have hs := cassels_solution_symm p q (hp.odd_of_ne_two hp2)
    (hq.odd_of_ne_two hq2) x y h
  have hd := cassels_p_dvd_y q p hq hp hq2 hp2
    (-y) (-x) (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hs
  simpa only [dvd_neg] using hd


#print axioms cassels_p_dvd_y
#print axioms cassels_q_dvd_x

end Catalan
