import Catalan.Cassels.BetweenPowers

namespace Catalan

lemma cassels_easy_q_dvd_x (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (q : ℤ) ∣ x := by
  by_contra hqx
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hoq : Odd q := hq.odd_of_ne_two hq2
  have hs := cassels_solution_symm p q hop hoq x y h
  have hn : ¬ (q : ℤ) ∣ -x := by simpa only [dvd_neg] using hqx
  obtain ⟨a, ha0, ha⟩ := cassels_bad_factor q p hq hp hp2
    (-y) (-x) (neg_ne_zero.mpr hx) hs hn
  let b : ℤ := -a
  have hb0 : b ≠ 0 := neg_ne_zero.mpr ha0
  have hbpow : y + 1 = b ^ p := by
    dsimp [b]
    rw [hop.neg_pow]
    linarith
  have hb1 : b ≠ 1 := by
    intro hb
    rw [hb, one_pow] at hbpow
    exact hy (by linarith)
  have hq3 : 3 ≤ q := by have ht := hq.two_le; omega
  have hbnd := cassels_between_powers p q hop hoq hq3 hqp b hb0 hb1
  have hyb : y = b ^ p - 1 := by linarith
  have hlo : (b ^ q - 1) ^ p < x ^ p := by
    rw [h, hyb]
    exact hbnd.1
  have hhi : x ^ p < (b ^ q) ^ p := by
    rw [h, hyb]
    exact hbnd.2
  have hlo' := hop.pow_lt_pow.mp hlo
  have hhi' := hop.pow_lt_pow.mp hhi
  omega


#print axioms cassels_easy_q_dvd_x

end Catalan
