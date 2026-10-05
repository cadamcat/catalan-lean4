module

public import Catalan.Stickelberger.MinusSpanDefs

/-!
# `Catalan.Stickelberger.MinusReflection`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma minus_theta_reflection (k : ℕ) (hk : 1 ≤ k) (hkp : k < p) :
    minusLinearMap p K (ΘS p K k + ΘS p K (p - k)) =
      minusLinearMap p K (pθ p K) := by
  classical
  let instMinusReflectionNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcoeff (T : R p K) (a : (ZMod p)ˣ) :
      (T * (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1)).coeff
          ((σ p K a)⁻¹) =
        T.coeff ((σ p K a)⁻¹) - T.coeff ((σ p K (-a))⁻¹) := by
    have hi : (σ p K a)⁻¹ * (ι p K)⁻¹ = (σ p K (-a))⁻¹ := by
      rw [ι, ← mul_inv_rev, ← σ_mul, neg_one_mul]
    rw [mul_sub, MonoidAlgebra.coeff_sub,
      Finsupp.sub_apply,
      MonoidAlgebra.coeff_mul_single_apply,
      MonoidAlgebra.coeff_mul_single_apply]
    simp only [inv_one, mul_one]
    rw [hi]
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  obtain ⟨a, ha⟩ := (σ_bijective p K).surjective g⁻¹
  have hag : (σ p K a)⁻¹ = g := by rw [ha, inv_inv]
  rw [← hag]
  simp only [minusLinearMap, LinearMap.mulRight_apply, map_add]
  rw [MonoidAlgebra.coeff_add]
  simp only [Finsupp.add_apply]
  have ha0 : 0 < (a : ZMod p).val :=
    (ZMod.val_pos).2 (Units.ne_zero a)
  have hap : (a : ZMod p).val < p := ZMod.val_lt _
  have hna0 : 0 < ((-a : (ZMod p)ˣ) : ZMod p).val :=
    (ZMod.val_pos).2 (Units.ne_zero (-a : (ZMod p)ˣ))
  have hnap : ((-a : (ZMod p)ˣ) : ZMod p).val < p :=
    ZMod.val_lt _
  have hsum_a :
      (((a : ZMod p).val * k / p : ℕ) : ℤ) +
          (((a : ZMod p).val * (p - k) / p : ℕ) : ℤ) =
        ((a : ZMod p).val : ℤ) - 1 := by
    have h := MinusGenerators.complementary_floor_sum p k
      (a : ZMod p).val (Fact.out : p.Prime) hk hkp ha0 hap
    have h' : (a : ZMod p).val * k / p + (a : ZMod p).val * (p - k) / p =
        (a : ZMod p).val - 1 := by simpa only [Nat.mul_comm] using h
    change (((a : ZMod p).val * k / p + (a : ZMod p).val * (p - k) / p : ℕ) : ℤ) =
      ((a : ZMod p).val : ℤ) - ((1 : ℕ) : ℤ)
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h'
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ (a : ZMod p).val)] using hcast
  have hsum_na :
      ((((-a : (ZMod p)ˣ) : ZMod p).val * k / p : ℕ) : ℤ) +
          ((((-a : (ZMod p)ˣ) : ZMod p).val * (p - k) / p : ℕ) : ℤ) =
        (((-a : (ZMod p)ˣ) : ZMod p).val : ℤ) - 1 := by
    have h := MinusGenerators.complementary_floor_sum p k
      ((-a : (ZMod p)ˣ) : ZMod p).val (Fact.out : p.Prime) hk hkp hna0 hnap
    have h' : ((-a : (ZMod p)ˣ) : ZMod p).val * k / p +
          ((-a : (ZMod p)ˣ) : ZMod p).val * (p - k) / p =
        ((-a : (ZMod p)ˣ) : ZMod p).val - 1 := by
      simpa only [Nat.mul_comm] using h
    change (((((-a : (ZMod p)ˣ) : ZMod p).val * k / p +
        ((-a : (ZMod p)ˣ) : ZMod p).val * (p - k) / p : ℕ)) : ℤ) =
      (((-a : (ZMod p)ˣ) : ZMod p).val : ℤ) - ((1 : ℕ) : ℤ)
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h'
    simpa only [Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ ((-a : (ZMod p)ˣ) : ZMod p).val)] using hcast
  rw [hcoeff, hcoeff, hcoeff]
  rw [ΘS_coeff, ΘS_coeff, ΘS_coeff, ΘS_coeff, pθ_coeff, pθ_coeff]
  omega

end Catalan
