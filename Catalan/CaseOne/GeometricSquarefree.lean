module

public import Mathlib

/-!
# `Catalan.CaseOne.GeometricSquarefree`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma geometricSum_squarefree (q n : ℕ) [Fact q.Prime] (hqn : ¬ q ∣ n) :
    Squarefree (∑ i ∈ Finset.range n, (Polynomial.X : Polynomial (ZMod q)) ^ i) := by
  have hsep :
      (Polynomial.X ^ n - Polynomial.C (1 : ZMod q)).Separable := by
    exact Polynomial.separable_X_pow_sub_C' q n (1 : ZMod q) hqn one_ne_zero
  apply (Polynomial.Separable.of_dvd hsep ?_).squarefree
  refine ⟨Polynomial.X - Polynomial.C (1 : ZMod q), ?_⟩
  simpa only [Polynomial.C_1] using
    (geom_sum_mul (Polynomial.X : Polynomial (ZMod q)) n).symm

end Catalan.UnitReduction
