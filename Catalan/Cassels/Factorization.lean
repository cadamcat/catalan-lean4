module

public import Catalan.Cassels.Divisibility

/-!
# `Catalan.Cassels.Factorization`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

/-- The integer factorization interface following Cassels' two divisibilities. -/
theorem cassels_factorization (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    ∃ (a b : ℤ) (u v : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ 0 < u ∧ 0 < v ∧
      x - 1 = (p : ℤ) ^ (q - 1) * a ^ q ∧ y = p * a * u ∧
      (x ^ p - 1) = (x - 1) * (p * u ^ q) ∧
      y + 1 = (q : ℤ) ^ (p - 1) * b ^ p ∧ x = q * b * v ∧
      (y ^ q + 1) = (y + 1) * (q * v ^ p) := by
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hoq : Odd q := hq.odd_of_ne_two hq2
  obtain ⟨b, v, hb, hv, hyb, hSq, hxb⟩ :=
    cassels_partial_q_relations p q hp hq hp2 hq2 x y hx hy h
      (cassels_q_dvd_x p q hp hq hp2 hq2 x y hx hy h)
  have hs := cassels_solution_symm p q hop hoq x y h
  have hpd : (p : ℤ) ∣ -y := dvd_neg.mpr
    (cassels_p_dvd_y p q hp hq hp2 hq2 x y hx hy h)
  obtain ⟨c, u, hc, hu, hxc, hSp, hyc⟩ :=
    cassels_partial_q_relations q p hq hp hq2 hp2 (-y) (-x)
      (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hs hpd
  have hxa : x - 1 = (p : ℤ) ^ (q - 1) * (-c) ^ q := by
    rw [hoq.neg_pow]
    linear_combination -hxc
  have hya : y = (p : ℤ) * (-c) * u := by
    linear_combination -hyc
  have hSp' : casselsCyclo p x = (p : ℤ) * u ^ q := by
    simpa only [neg_neg] using hSp
  have hfactorq : y ^ q + 1 = (y + 1) * casselsCyclo q (-y) := by
    have hf := int_pow_sub_one_factor q (-y)
    rw [hoq.neg_pow] at hf
    linear_combination -hf
  refine ⟨-c, b, u, v, neg_ne_zero.mpr hc, hb, hu, hv, hxa, hya, ?_, hyb, hxb, ?_⟩
  · rw [int_pow_sub_one_factor, hSp']
  · rw [hfactorq, hSq]

#print axioms cassels_factorization

end Catalan
