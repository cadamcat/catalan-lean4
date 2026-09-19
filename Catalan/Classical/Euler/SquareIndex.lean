import Catalan.Classical.Euler.Sequence
import Mathlib

namespace Catalan.Euler

lemma pell_y_plus_one_twice_square_of_x_square_trivial
    (htriv : ∀ n a : ℕ, pellX n = a ^ 2 → n = 0)
    (n a : ℕ) (h : pellY n + 1 = 2 * a ^ 2) : n = 1 := by
  have hsquare (u v w : ℕ) (hc : u.Coprime v) (he : u * v = w ^ 2) :
      ∃ t : ℕ, u = t ^ 2 := by
    apply exists_eq_pow_of_mul_eq_pow ?_ he
    change IsUnit (Nat.gcd u v)
    rw [hc.gcd_eq_one]
    exact isUnit_one
  have hnodd : Odd n := (pell_y_odd_iff n).mp (by
    apply Nat.odd_iff.mpr
    omega)
  obtain ⟨m, hm⟩ := hnodd
  have hn : n = 2 * m + 1 := by omega
  subst n
  have hprod : pellX m * pellY (m + 1) = a ^ 2 := by
    have hy := pell_y_odd m
    nlinarith only [hy, h]
  have hstep : pellY (m + 1) = pellX m + 2 * pellY m := by
    simpa only [pellY, pellX, Nat.mul_comm] using Pell.yn_succ (by decide : 1 < 2) m
  by_cases hXm : Odd (pellX m)
  · have hcop : (pellX m).Coprime (pellY (m + 1)) := by
      rw [hstep, Nat.coprime_self_add_right]
      exact hXm.coprime_two_right.mul_right (pell_xy_coprime m)
    obtain ⟨b, hb⟩ := hsquare (pellX m) (pellY (m + 1)) a hcop hprod
    have hm0 := htriv m b hb
    omega
  · have hXeven : Even (pellX m) := (Nat.even_or_odd _).resolve_right hXm
    obtain ⟨u, hu⟩ := hXeven
    have hXu : pellX m = 2 * u := by omega
    have hYnext : pellY (m + 1) = 2 * (u + pellY m) := by
      rw [hstep, hXu]
      ring
    have h4 : a ^ 2 = 4 * (u * (u + pellY m)) := by
      rw [← hprod, hXu, hYnext]
      ring
    have hadvd : 2 ∣ a := Nat.prime_two.dvd_of_dvd_pow (by
      rw [h4]
      exact dvd_mul_of_dvd_left (by decide : 2 ∣ 4) _)
    obtain ⟨c, hc⟩ := hadvd
    have hhalf : u * (u + pellY m) = c ^ 2 := by
      rw [hc] at h4
      nlinarith only [h4]
    have hcopUY : u.Coprime (pellY m) := by
      apply Nat.Coprime.of_dvd_left _ (pell_xy_coprime m)
      rw [hXu]
      exact dvd_mul_left u 2
    have hcopHalf : (u + pellY m).Coprime u :=
      (Nat.coprime_self_add_right.mpr hcopUY).symm
    obtain ⟨d, hd⟩ := hsquare (u + pellY m) u c hcopHalf (by
      simpa only [Nat.mul_comm] using hhalf)
    have hYsquare : pellY (m + 1) = 2 * d ^ 2 := by rw [hYnext, hd]
    have hmNotEven : ¬ Even m := fun he => hXm ((pell_x_odd_iff m).mpr he)
    have hmOdd : Odd m := (Nat.even_or_odd m).resolve_left hmNotEven
    obtain ⟨k, hk⟩ := hmOdd
    have hind : m + 1 = 2 * (k + 1) := by omega
    rw [hind, pell_y_double] at hYsquare
    have hprodK : pellX (k + 1) * pellY (k + 1) = d ^ 2 := by
      nlinarith only [hYsquare]
    obtain ⟨e, he⟩ := hsquare (pellX (k + 1)) (pellY (k + 1)) d
      (pell_xy_coprime (k + 1)) hprodK
    have hk0 := htriv (k + 1) e he
    omega

end Catalan.Euler
