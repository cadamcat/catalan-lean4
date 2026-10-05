module

public import Catalan.Wieferich.Coefficient
public import Catalan.Cyclotomic.GroupRingMul

/-!
# `Catalan.Stickelberger.MinusDefs`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators IsMulCommutative
open NumberField
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

noncomputable def θminus (k : ℕ) : R p K :=
  (ΘS p K (k + 1) - ΘS p K k) * (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1)

lemma ΘS_coeff (k : ℕ) (a : (ZMod p)ˣ) :
    (ΘS p K k).coeff ((σ p K a)⁻¹) = (((a : ZMod p).val * k / p : ℕ) : ℤ) := by
  classical
  have hinj (b c : (ZMod p)ˣ) : (σ p K b)⁻¹ = (σ p K c)⁻¹ ↔ b = c := by
    rw [inv_inj]
    exact (σ_bijective p K).injective.eq_iff
  simp [ΘS, Finsupp.single_apply, hinj]

lemma θminus_coeff (k : ℕ) (a : (ZMod p)ˣ) :
    (θminus p K k).coeff ((σ p K a)⁻¹) =
      ((((a : ZMod p).val * (k + 1) / p : ℕ) : ℤ) -
        (((a : ZMod p).val * k / p : ℕ) : ℤ)) -
      (((((-a : (ZMod p)ˣ) : ZMod p).val * (k + 1) / p : ℕ) : ℤ) -
        ((((-a : (ZMod p)ˣ) : ZMod p).val * k / p : ℕ) : ℤ)) := by
  have hi : (σ p K a)⁻¹ * (ι p K)⁻¹ = (σ p K (-a))⁻¹ := by
    rw [ι, ← mul_inv_rev, ← σ_mul, neg_one_mul]
  simp only [θminus, mul_sub, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_mul_single_apply, inv_one, mul_one, hi, ΘS_coeff]

lemma θminus_eq_minusPart (k : ℕ) :
    θminus p K k = A1e.minusPart p K (ΘS p K (k + 1) - ΘS p K k) := by
  have instGalComm : IsMulCommutative (G p K) :=
    IsCyclotomicExtension.isMulCommutative {p} ℚ K
  exact mul_comm _ _

theorem θminus_weight (k : ℕ) : weight p K (θminus p K k) = 0 := by
  simp only [θminus, weight_mul, weight_sub, weight_single, sub_self, mul_zero]

end Catalan
