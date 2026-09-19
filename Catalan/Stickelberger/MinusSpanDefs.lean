import Catalan.Stickelberger.MinusStability
import Catalan.Stickelberger.MinusFloor

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

def minusLinearMap : R p K →ₗ[ℤ] R p K :=
  LinearMap.mulRight ℤ (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1)

def minusGeneratorSpan : Submodule ℤ (R p K) :=
  Submodule.span ℤ (Set.range (fun k : Fin ((p - 1) / 2) => θminus p K (k.val + 1)))

lemma pθ_coeff (a : (ZMod p)ˣ) :
    (pθ p K).coeff ((σ p K a)⁻¹) = ((a : ZMod p).val : ℤ) := by
  classical
  have hinj (b c : (ZMod p)ˣ) : (σ p K b)⁻¹ = (σ p K c)⁻¹ ↔ b = c := by
    rw [inv_inj]
    exact (σ_bijective p K).injective.eq_iff
  simp [pθ, Finsupp.single_apply, hinj]

lemma ΘS_one : ΘS p K 1 = 0 := by
  classical
  unfold ΘS
  apply Finset.sum_eq_zero
  intro a _
  simp only [Nat.mul_one, Nat.div_eq_of_lt (ZMod.val_lt (a : ZMod p)),
    Nat.cast_zero, MonoidAlgebra.single_zero]

end Catalan
