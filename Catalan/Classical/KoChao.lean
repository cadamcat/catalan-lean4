import Catalan.Classical.KoChao.Factors
import Catalan.Classical.KoChao.PellDivisibility
import Catalan.Classical.KoChao.SecondCongruence
import Catalan.Classical.Euler

set_option autoImplicit false
namespace Catalan

theorem koChao_p_two (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ q + 1) : (x = 3 ∨ x = -3) ∧ y = 2 ∧ q = 3 := by
  have hq3 : q = 3 := by
    by_contra hq3
    have hq5 : 5 ≤ q := by
      have hqge := hq.two_le
      have hqodd := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
      omega
    have hqx := KoChao.square_base_q_dvd_x q hq hq2 x y hx hy h
    have hxodd := (KoChao.square_base_positive_even q hq hq2 x y hx hy h).2.2
    obtain ⟨z, a, b, hz, ha, hb, _, hminus, hplus, hcop⟩ :=
      KoChao.square_base_oriented_factors q hq hq2 x y hx hy hxodd h
    have hqz : (q : ℤ) ∣ z := by
      rcases hz with hz | hz
      · simpa only [hz] using hqx
      · simpa only [hz, dvd_neg] using hqx
    have hqz3 := KoChao.oriented_second_congruence q hq hq5 z a b ha hb hminus hplus hcop
    exact hq3 (KoChao.prime_eq_three_of_two_congruences q hq z hqz hqz3)
  have heuler := euler_square_cube x y hx hy (by simpa only [hq3] using h)
  exact ⟨heuler.1, heuler.2, hq3⟩

end Catalan
