import Catalan.Wieferich.Defs
import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma testTheta_coefficient (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    (testTheta p K).coeff ((σ p K a)⁻¹) =
      if 2 * (a : ZMod p).val < p then -1 else 1
 := by
  classical
  have hinj (b c : (ZMod p)ˣ) : (σ p K b)⁻¹ = (σ p K c)⁻¹ ↔ b = c := by
    rw [inv_inj]
    exact (σ_bijective p K).injective.eq_iff
  have hcoeff (b : (ZMod p)ˣ) :
      (ΘS p K 2).coeff ((σ p K b)⁻¹) = (((b : ZMod p).val * 2 / p : ℕ) : ℤ) := by
    simp [ΘS, Finsupp.single_apply, hinj]
  have hindex : (ι p K)⁻¹ * (σ p K a)⁻¹ = (σ p K (-a))⁻¹ := by
    rw [ι, ← mul_inv_rev, ← σ_mul, mul_neg_one]
  rw [testTheta, minusPart, sub_mul, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_single_one_mul, one_mul,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, hindex, hcoeff, hcoeff]
  have hapos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr (Units.ne_zero a)
  have halt : (a : ZMod p).val < p := ZMod.val_lt _
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2
  have hmid : 2 * (a : ZMod p).val ≠ p := by omega
  have hneg : ((-a : (ZMod p)ˣ) : ZMod p).val = p - (a : ZMod p).val := by
    rw [Units.val_neg, ZMod.neg_val, if_neg (Units.ne_zero a)]
  rw [hneg]
  split_ifs with h
  · have h0 : (a : ZMod p).val * 2 / p = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : (p - (a : ZMod p).val) * 2 / p = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp only [h0, h1, Nat.cast_zero, Nat.cast_one, zero_sub]
  · have h1 : (a : ZMod p).val * 2 / p = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have h0 : (p - (a : ZMod p).val) * 2 / p = 0 := Nat.div_eq_of_lt (by omega)
    simp only [h0, h1, Nat.cast_zero, Nat.cast_one, sub_zero]

end Catalan.A1e

