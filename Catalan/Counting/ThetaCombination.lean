module

public import Catalan.Cyclotomic.GroupRingSums
public import Catalan.Stickelberger.MinusIndependent
public import Catalan.Stickelberger.MinusNorm

/-!
# `Catalan.Counting.ThetaCombination`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

def thetaCombination (c : Fin ((p - 1) / 2) → ℤ) : R p K :=
  ∑ i, c i • θminus p K (i.val + 1)

lemma thetaCombination_injective : Function.Injective (thetaCombination p K) :=
  θminus_linIndep p K

lemma thetaCombination_weight (c : Fin ((p - 1) / 2) → ℤ) :
    weight p K (thetaCombination p K c) = 0 := by
  simp only [thetaCombination, weight_sum, weight_zsmul, θminus_weight, mul_zero,
    Finset.sum_const_zero]

lemma thetaCombination_size (c : Fin ((p - 1) / 2) → ℤ) :
    size p K (thetaCombination p K c) ≤ ((p : ℤ) - 1) * ∑ i, |c i| := by
  calc
    size p K (thetaCombination p K c) ≤ ∑ i, size p K (c i • θminus p K (i.val + 1)) :=
      size_sum_le p K Finset.univ _
    _ = ∑ i, |c i| * ((p : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [size_zsmul, θminus_size_eq p K (i.val + 1) (by omega) (by have := i.isLt; omega)]
    _ = ((p : ℤ) - 1) * ∑ i, |c i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end Catalan
