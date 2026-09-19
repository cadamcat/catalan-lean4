import Catalan.Cassels.DenominatorDefs

open scoped BigOperators

namespace Catalan

/-- Casting the signed integer product recovers the rational numerator. -/
lemma casselsCoeff_eq_numProd (p q k : ℕ) :
    casselsCoeff p q k = (casselsNumProd p q k : ℚ) /
      ((q : ℚ) ^ k * (k.factorial : ℚ)) := by
  simp only [casselsCoeff, casselsNumProd, Int.cast_prod, Int.cast_sub,
    Int.cast_mul, Int.cast_natCast]

/-- Rational reconstruction once the factorial decomposition and exact
integer numerator division have been established. -/
lemma cassels_coeff_eq_of_factorization (p q k u : ℕ) (B : ℤ)
    (hq : q ≠ 0) (hu : u ≠ 0)
    (hfac : k.factorial = q ^ padicValNat q k.factorial * u)
    (hnum : casselsNumProd p q k = (u : ℤ) * B) :
    casselsCoeff p q k = (B : ℚ) / (q : ℚ) ^ casselsDenExp q k := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hfacQ : (k.factorial : ℚ) =
      (q : ℚ) ^ padicValNat q k.factorial * (u : ℚ) := by
    exact_mod_cast hfac
  have hnumQ : (casselsNumProd p q k : ℚ) = (u : ℚ) * (B : ℚ) := by
    exact_mod_cast hnum
  rw [casselsCoeff_eq_numProd, hnumQ, hfacQ, casselsDenExp, pow_add]
  field_simp

#print axioms casselsCoeff_eq_numProd
#print axioms cassels_coeff_eq_of_factorization

end Catalan
