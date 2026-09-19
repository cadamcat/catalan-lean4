import Mathlib

namespace Catalan

/-- An integer whose absolute value is an odd power is itself that power,
after choosing the sign of the root. -/
lemma int_eq_odd_pow_of_natAbs_eq_pow (n : ℕ) (hn : Odd n)
    (z : ℤ) (r : ℕ) (h : z.natAbs = r ^ n) :
    ∃ a : ℤ, z = a ^ n := by
  have habs : |z| = (r : ℤ) ^ n := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℤ)) h
  by_cases hz : 0 ≤ z
  · exact ⟨r, by simpa only [abs_of_nonneg hz] using habs⟩
  · refine ⟨-(r : ℤ), ?_⟩
    rw [hn.neg_pow]
    rw [abs_of_neg (lt_of_not_ge hz)] at habs
    omega

/-- Cassels' coprime-factor step: both coprime integer factors of an odd
perfect power are perfect powers. -/
lemma cassels_coprime_power_factors (n : ℕ) (hn : Odd n)
    (A B C : ℤ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hg : Int.gcd A B = 1) (h : A * B = C ^ n) :
    ∃ a b : ℤ, A = a ^ n ∧ B = b ^ n := by
  have hnat : A.natAbs * B.natAbs = C.natAbs ^ n := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h
  have hgNat : IsUnit (GCDMonoid.gcd A.natAbs B.natAbs) := by
    change IsUnit (Nat.gcd A.natAbs B.natAbs)
    change Int.gcd A B = 1 at hg
    rw [show Nat.gcd A.natAbs B.natAbs = 1 from hg]
    exact isUnit_one
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hgNat hnat
  have hgNat' : IsUnit (GCDMonoid.gcd B.natAbs A.natAbs) := by
    simpa only [gcd_comm] using hgNat
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hgNat' (by
    simpa only [Nat.mul_comm] using hnat)
  obtain ⟨a', ha'⟩ := int_eq_odd_pow_of_natAbs_eq_pow n hn A a ha
  obtain ⟨b', hb'⟩ := int_eq_odd_pow_of_natAbs_eq_pow n hn B b hb
  exact ⟨a', b', ha', hb'⟩

#print axioms int_eq_odd_pow_of_natAbs_eq_pow
#print axioms cassels_coprime_power_factors

end Catalan
