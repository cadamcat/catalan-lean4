module

public import Catalan.Cassels.DenominatorDefs

/-!
# `Catalan.Cassels.FactorialCore`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators

namespace Catalan

theorem cassels_factorial_core_spec
    (q k : ℕ) (hq : q.Prime) :
    0 < casselsFactorialCore q k ∧
    k.factorial = q ^ padicValNat q k.factorial * casselsFactorialCore q k ∧
    (¬ q ∣ casselsFactorialCore q k) ∧
    q.Coprime (casselsFactorialCore q k) := by
  let n : ℕ := k.factorial
  let e : ℕ := padicValNat q n
  let u : ℕ := n / q ^ e
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.factorial_pos k
  have hpow : q ^ e ∣ n := by
    exact (padicValNat_dvd_iff_le_of_ne_one hq.ne_one hn.ne').2 le_rfl
  have hdecomp : n = q ^ e * u := by
    dsimp [u]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hpow).symm
  have hu : 0 < u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos h
    rw [hu0, mul_zero] at hdecomp
    exact hn.ne' hdecomp
  have hnot : ¬ q ∣ u := by
    intro hqu
    have hmul : q ^ e * q ∣ q ^ e * u := Nat.mul_dvd_mul_left _ hqu
    have hs : q ^ (e + 1) ∣ n := by
      rw [pow_succ, hdecomp]
      exact hmul
    have hle : e + 1 ≤ padicValNat q n :=
      (padicValNat_dvd_iff_le_of_ne_one hq.ne_one hn.ne').1 hs
    exact (Nat.not_succ_le_self e) hle
  have hcop : q.Coprime u := hq.coprime_iff_not_dvd.2 hnot
  simpa only [casselsFactorialCore, n, e, u] using ⟨hu, hdecomp, hnot, hcop⟩

theorem cassels_numProd_not_dvd
    (p q k : ℕ) (hq : q.Prime) (hqp : ¬ q ∣ p) :
    ¬ (q : ℤ) ∣ casselsNumProd p q k := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  unfold casselsNumProd
  apply hqZ.not_dvd_finsetProd
  intro i hi hdiv
  apply hqp
  have hqi : (q : ℤ) ∣ (i : ℤ) * (q : ℤ) := by
    exact dvd_mul_of_dvd_right (dvd_refl (q : ℤ)) _
  have hadd : (q : ℤ) ∣ ((p : ℤ) - (i : ℤ) * (q : ℤ)) + (i : ℤ) * (q : ℤ) :=
    dvd_add hdiv hqi
  have hpZ : (q : ℤ) ∣ (p : ℤ) := by simpa using hadd
  simpa using (Int.natCast_dvd.mp hpZ)

#print axioms cassels_factorial_core_spec
#print axioms cassels_numProd_not_dvd

end Catalan
