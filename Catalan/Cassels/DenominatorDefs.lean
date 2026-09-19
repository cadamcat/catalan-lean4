import Catalan.Cassels.Defs

open scoped BigOperators

namespace Catalan

/-- The signed numerator product of the generalized binomial coefficient. -/
def casselsNumProd (p q k : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, ((p : ℤ) - (i : ℤ) * (q : ℤ))

/-- The factorial after removing its full `q`-power. -/
def casselsFactorialCore (q k : ℕ) : ℕ :=
  k.factorial / q ^ padicValNat q k.factorial

/-- The candidate integral numerator; exactness is proved separately. -/
def casselsCoeffNum (p q k : ℕ) : ℤ :=
  casselsNumProd p q k / (casselsFactorialCore q k : ℤ)

end Catalan
