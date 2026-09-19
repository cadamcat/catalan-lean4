import Catalan.Cassels.Denominator
import Catalan.Mihailescu.Ideal

set_option autoImplicit false
open scoped BigOperators Classical
open NumberField
noncomputable section
namespace Catalan.Runge

abbrev D (q k : ℕ) : ℕ := casselsDenExp q k

def binomRat (a : ℚ) (k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range k, (a - (j : ℚ))) / (Nat.factorial k : ℚ)

def errorBound (q m : ℕ) (X : ℝ) : ℝ :=
  ((q : ℝ) ^ D q m * ((2 * m).choose (m + 1) : ℝ)) /
    ((1 - X⁻¹) ^ (2 * m + 1) * X)

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance definitionsGalFintype : Fintype (G p K) := Fintype.ofFinite _

def EvenCoefficients (Theta : R p K) : Prop :=
  ∀ g : G p K, Theta.coeff (ι p K * g) = Theta.coeff g

def rungeCoeff (q : ℕ) (Theta : R p K) (k : ℕ) : K :=
  ∑ f : G p K → Fin (k + 1),
    if (∑ g : G p K, (f g).val) = k then
      ∏ g : G p K,
        (algebraMap ℚ K (binomRat ((Theta.coeff g : ℚ) / (q : ℚ)) (f g).val) *
          (-g (ζ p K)) ^ (f g).val)
    else 0

def rungeApprox (q : ℕ) (Theta : R p K) (m : ℕ) (x : ℤ) : K :=
  (q : K) ^ D q m *
    ∑ k ∈ Finset.range (m + 1), rungeCoeff p K q Theta k * (x : K) ^ (m - k)

end Cyclotomic
end Catalan.Runge
