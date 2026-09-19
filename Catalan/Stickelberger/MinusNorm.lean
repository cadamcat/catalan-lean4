import Catalan.Stickelberger.MinusDefs
import Catalan.Stickelberger.MinusFloor

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance instMinusNormFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma θminus_coeff_eq_neg_one_or_one (k : ℕ) (hk : 1 ≤ k)
    (hk' : k ≤ (p - 1) / 2) (a : (ZMod p)ˣ) :
    (θminus p K k).coeff ((σ p K a)⁻¹) = -1 ∨
      (θminus p K k).coeff ((σ p K a)⁻¹) = 1 := by
  have ha0 : 0 < (a : ZMod p).val := ZMod.val_pos.mpr (Units.ne_zero a)
  have hap : (a : ZMod p).val < p := ZMod.val_lt _
  have hkp : k < p := by omega
  have hkp1 : k + 1 < p := by omega
  have hsN := MinusGenerators.complementary_floor_sum p (a : ZMod p).val (k + 1)
    hp.out ha0 hap (by omega) hkp1
  have hbN := MinusGenerators.complementary_floor_sum p (a : ZMod p).val k
    hp.out ha0 hap (by omega) hkp
  have hs := congrArg (fun n : ℕ => (n : ℤ)) hsN
  have hb := congrArg (fun n : ℕ => (n : ℤ)) hbN
  simp only [Nat.add_sub_cancel, Nat.cast_add] at hs
  simp only [Nat.cast_add, Nat.cast_sub hk, Nat.cast_one] at hb
  have hneg : ((-a : (ZMod p)ˣ) : ZMod p).val = p - (a : ZMod p).val := by
    rw [Units.val_neg, ZMod.neg_val, if_neg (Units.ne_zero a)]
  simp only [θminus_coeff, hneg]
  rcases MinusGenerators.floor_step_zero_or_one p (a : ZMod p).val k hap with hd | hd
  · left; omega
  · right; omega

lemma θminus_size_eq (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ (p - 1) / 2) :
    size p K (θminus p K k) = (p : ℤ) - 1 := by
  classical
  rw [size_eq_sum]
  calc
    (∑ τ : G p K, |(θminus p K k).coeff τ|) =
        ∑ a : (ZMod p)ˣ, |(θminus p K k).coeff ((σ p K a)⁻¹)| := by
      exact (((Equiv.inv (G p K)).bijective.comp (σ_bijective p K)).sum_comp _).symm
    _ = ∑ _a : (ZMod p)ˣ, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rcases θminus_coeff_eq_neg_one_or_one p K k hk hk' a with ha | ha <;>
        rw [ha] <;> norm_num
    _ = (p : ℤ) - 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ZMod.card_units, Nat.cast_sub hp.out.one_le, Nat.cast_one]

theorem θminus_size_le (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ (p - 1) / 2) : size p K (θminus p K k) ≤ p - 1 := by
  exact (θminus_size_eq p K k hk hk').le

end Catalan
