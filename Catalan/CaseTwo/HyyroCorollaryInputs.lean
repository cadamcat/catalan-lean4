module

public import Catalan.Cassels.Hyyro

/-!
# `Catalan.CaseTwo.HyyroCorollaryInputs`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma hyyro_implies_h9
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p < q) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (8 : ℝ) * ((4 / 5 : ℝ) * (q : ℝ)) ^ q ≤ (|x| : ℝ) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq5 : 5 ≤ q := by
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two hq2
    omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq5
  have hH : (p : ℝ) ^ (q - 1) * ((q : ℝ) - 1) ^ q + 1 ≤ (|x| : ℝ) := by
    exact_mod_cast hyyro_bound p q hp hq hp2 hq2 x y hx hy h
  have hP : (8 : ℝ) ≤ (p : ℝ) ^ (q - 1) := by
    calc
      (8 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      _ ≤ (p : ℝ) ^ (q - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hQ : ((4 / 5 : ℝ) * (q : ℝ)) ^ q ≤ ((q : ℝ) - 1) ^ q :=
    pow_le_pow_left₀ (by positivity) (by linarith) q
  calc
    (8 : ℝ) * ((4 / 5 : ℝ) * (q : ℝ)) ^ q ≤
        (p : ℝ) ^ (q - 1) * ((q : ℝ) - 1) ^ q :=
      mul_le_mul hP hQ (by positivity) (by positivity)
    _ ≤ (|x| : ℝ) := by linarith

lemma cassels_x_mod_one
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    x ≡ 1 [ZMOD (p : ℤ)] := by
  have instPrimeModulus : Fact p.Prime := ⟨hp⟩
  have hy0 : (y : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mpr
      (cassels_p_dvd_y p q hp hq hp2 hq2 x y hx hy h)
  have hmod := congrArg (fun n : ℤ => (n : ZMod p)) h
  have hx1 : (x : ZMod p) = 1 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_one, hy0,
      zero_pow hq.ne_zero, zero_add, ZMod.pow_card] using hmod
  exact (ZMod.intCast_eq_intCast_iff x 1 p).mp (by simpa using hx1)


end Catalan
