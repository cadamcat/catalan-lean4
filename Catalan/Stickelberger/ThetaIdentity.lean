module

public import Catalan.Cyclotomic.Basic

/-!
# `Catalan.Stickelberger.ThetaIdentity`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField

noncomputable section
namespace Catalan

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [hcycl : IsCyclotomicExtension {p} ℚ K]

local instance instThetaIdentityFintypeG : Fintype (G p K) := Fintype.ofFinite _

theorem theta_identity (a : (ZMod p)ˣ) :
    ((a : ZMod p).val : ℤ) • pθ p K -
      MonoidAlgebra.single (σ p K a) 1 * pθ p K =
        (p : ℤ) • ΘS p K ((a : ZMod p).val) := by
  have hmul (b : (ZMod p)ˣ) :
      σ p K a * (σ p K (b * a))⁻¹ = (σ p K b)⁻¹ := by
    rw [σ_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsum :
      MonoidAlgebra.single (σ p K a) 1 * pθ p K =
        ∑ b : (ZMod p)ˣ,
          MonoidAlgebra.single (σ p K b)⁻¹
            ((((b * a : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ) := by
    unfold pθ
    rw [Finset.mul_sum]
    calc
      (∑ b : (ZMod p)ˣ,
          MonoidAlgebra.single (σ p K a) 1 *
            MonoidAlgebra.single (σ p K b)⁻¹
              ((((b : ZMod p).val : ℕ) : ℤ))) =
          ∑ b : (ZMod p)ˣ,
            MonoidAlgebra.single (σ p K a * (σ p K b)⁻¹)
              ((((b : ZMod p).val : ℕ) : ℤ)) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [MonoidAlgebra.single_mul_single]
        simp
      _ = ∑ b : (ZMod p)ˣ,
            MonoidAlgebra.single (σ p K b)⁻¹
              ((((b * a : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ) := by
        rw [← Equiv.sum_comp (Equiv.mulRight a)]
        apply Finset.sum_congr rfl
        intro b hb
        change MonoidAlgebra.single (σ p K a * (σ p K (b * a))⁻¹)
            ((((b * a : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ) = _
        rw [hmul]
  have hval (b : (ZMod p)ˣ) :
      (((b * a : (ZMod p)ˣ) : ZMod p).val) =
        ((b : ZMod p).val * (a : ZMod p).val) % p := by
    rw [Units.val_mul, ZMod.val_mul]
  have hdiv (b : (ZMod p)ˣ) :
      p * (((b : ZMod p).val * (a : ZMod p).val) / p) +
          (((b * a : (ZMod p)ˣ) : ZMod p).val) =
        (b : ZMod p).val * (a : ZMod p).val := by
    rw [hval]
    exact Nat.div_add_mod _ _
  rw [hsum]
  unfold pθ ΘS
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [MonoidAlgebra.smul_single]
  rw [← MonoidAlgebra.single_sub]
  congr 1
  change (a : ZMod p).val * (b : ZMod p).val -
      (((b * a : (ZMod p)ˣ) : ZMod p).val : ℤ) =
    (p : ℤ) * ((((b : ZMod p).val * (a : ZMod p).val) / p : ℕ) : ℤ)
  have hdivZ :
      (p : ℤ) * ((((b : ZMod p).val * (a : ZMod p).val) / p : ℕ) : ℤ) +
          (((b * a : (ZMod p)ˣ) : ZMod p).val : ℤ) =
        (((b : ZMod p).val * (a : ZMod p).val : ℕ) : ℤ) := by
    exact_mod_cast hdiv b
  norm_num only [Nat.cast_mul] at hdivZ
  nlinarith [hdivZ]


end Catalan
