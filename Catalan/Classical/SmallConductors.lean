import Catalan.Mihailescu.RadiusTwoExclusion
import Catalan.CaseTwo.HyyroCorollaryInputs
import Catalan.Stickelberger.MinusMihailescu

noncomputable section
namespace Catalan

lemma small_odd_prime_no_solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q)
    (hsmall : p = 3 ∨ p = 5 ∨ p = 7)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) : x ^ p ≠ y ^ q + 1 := by
  intro h
  have instPrimeP : Fact p.Prime := ⟨hp⟩
  have instPrimeQ : Fact q.Prime := ⟨hq⟩
  have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  have instCyclo : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨T, hT, hTne, hTs⟩ :=
    small_conductor_aug_witness p (CyclotomicField p ℚ) q hp2 hq2 hsmall x y hx hy h
  have hx1 := cassels_x_mod_one p q hp hq hp2 hq2 x y hx hy h
  have hbound : (|x| : ℝ) ≥ 8 * (0.8 * (q : ℝ)) ^ q := by
    simpa only [show (4 / 5 : ℝ) = 0.8 by norm_num] using
      hyyro_implies_h9 p q hp hq hp2 hq2 hpq x y hx hy h
  exact hTne (aug_two_eq_zero p (CyclotomicField p ℚ) q x hp2 hpq hx1 hbound
    T hT.1 hT.2 hTs.le)

theorem nagell_p_three (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 3 ≠ y ^ q + 1 := by
  intro h
  by_cases hq3 : q = 3
  · subst q
    exact cassels_equal_exponents_false 3 Nat.prime_three (by decide) x y hx hy h
  · have h3q : 3 < q := by have := hq.two_le; omega
    exact small_odd_prime_no_solution 3 q Nat.prime_three hq (by decide) hq2 h3q
      (Or.inl rfl) x y hx hy h

end Catalan
