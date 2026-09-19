import Catalan.Cassels.FactorialCore
import Catalan.Cassels.FactorialTransfer
import Catalan.Cassels.CoefficientReconstruction

namespace Catalan

/-- The prime-to-`q` part of the factorial divides the signed product, so
the candidate integral numerator is an exact quotient. -/
lemma cassels_coeffNum_mul_core (p q k : ℕ) (hq : q.Prime) :
    casselsNumProd p q k =
      (casselsFactorialCore q k : ℤ) * casselsCoeffNum p q k := by
  obtain ⟨hpos, hfac, _, hcop⟩ := cassels_factorial_core_spec q k hq
  have hcoreDvd : casselsFactorialCore q k ∣ k.factorial := by
    exact ⟨q ^ padicValNat q k.factorial, by simpa only [Nat.mul_comm] using hfac⟩
  have hdvd := cassels_factorial_divisor_dvd_numProd
    p q (casselsFactorialCore q k) k hpos hcoreDvd hcop
  unfold casselsCoeffNum
  simpa only [Int.mul_comm] using (Int.ediv_mul_cancel hdvd).symm

/-- The exact denominator identity does not require `q ∤ p`. -/
lemma cassels_coeff_eq_coeffNum (p q k : ℕ) (hq : q.Prime) :
    casselsCoeff p q k =
      (casselsCoeffNum p q k : ℚ) / (q : ℚ) ^ casselsDenExp q k := by
  obtain ⟨hpos, hfac, _, _⟩ := cassels_factorial_core_spec q k hq
  exact cassels_coeff_eq_of_factorization p q k (casselsFactorialCore q k)
    (casselsCoeffNum p q k) hq.ne_zero hpos.ne' hfac
    (cassels_coeffNum_mul_core p q k hq)

/-- Divisibility of the chosen numerator would imply divisibility of the
original product, contradicting the factorwise prime argument. -/
lemma cassels_coeffNum_not_dvd (p q k : ℕ)
    (hq : q.Prime) (hqp : ¬ q ∣ p) :
    ¬ (q : ℤ) ∣ casselsCoeffNum p q k := by
  intro hdiv
  apply cassels_numProd_not_dvd p q k hq hqp
  rw [cassels_coeffNum_mul_core p q k hq]
  exact dvd_mul_of_dvd_right hdiv _

/-- Cassels' coefficient denominator lemma with the original signature. The
numerator function is given explicitly by integer division. -/
lemma cassels_coeff_denominator (p q : ℕ) (hq : q.Prime) (hqp : ¬ q ∣ p) :
    ∃ B : ℕ → ℤ, (∀ k, ¬ (q : ℤ) ∣ B k) ∧
      ∀ k, casselsCoeff p q k = (B k : ℚ) / (q : ℚ) ^ casselsDenExp q k := by
  exact ⟨casselsCoeffNum p q, fun k => cassels_coeffNum_not_dvd p q k hq hqp,
    fun k => cassels_coeff_eq_coeffNum p q k hq⟩

/-- The immediate valuation consequence of the coefficient-denominator lemma. -/
lemma cassels_coeff_padicValRat (p q : ℕ) (hq : q.Prime)
    (hqp : ¬ q ∣ p) (k : ℕ) :
    padicValRat q (casselsCoeff p q k) = -(casselsDenExp q k : ℤ) := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨B, hBunit, hB⟩ := cassels_coeff_denominator p q hq hqp
  have hb0 : B k ≠ 0 := by
    intro hb
    apply hBunit k
    rw [hb]
    exact dvd_zero _
  have hbQ : (B k : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [hB k, padicValRat.div hbQ (pow_ne_zero _ hqQ),
    padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (hBunit k),
    padicValRat.pow, padicValRat.self hq.one_lt, mul_one]
  simp only [Nat.cast_zero, zero_sub]

#print axioms cassels_coeffNum_mul_core
#print axioms cassels_coeff_eq_coeffNum
#print axioms cassels_coeffNum_not_dvd
#print axioms cassels_coeff_denominator
#print axioms cassels_coeff_padicValRat

end Catalan
