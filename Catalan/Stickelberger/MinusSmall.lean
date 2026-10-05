module

public import Catalan.Stickelberger.MinusDefs

/-!
# `Catalan.Stickelberger.MinusSmall`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private lemma minus_basis_coeff (a : (ZMod p)ˣ) :
    (MonoidAlgebra.single 1 (1 : ℤ) - MonoidAlgebra.single (ι p K) 1).coeff ((σ p K a)⁻¹) =
      (if (a : ZMod p).val = 1 then 1 else 0) -
      (if (a : ZMod p).val = p - 1 then 1 else 0) := by
  classical
  let pNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hσone : σ p K 1 = 1 := (IsCyclotomicExtension.Rat.galEquivZMod p K).symm.map_one
  have hσinv : (σ p K a)⁻¹ = σ p K a⁻¹ :=
    ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm.map_inv a).symm
  have hvalOne : a = 1 ↔ (a : ZMod p).val = 1 := by
    constructor
    · rintro rfl
      exact ZMod.val_one'' (Fact.out : p.Prime).ne_one
    · intro h
      exact Units.ext ((ZMod.val_eq_one (Fact.out : p.Prime).one_lt _).mp h)
  have hmOne : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
    change (-1 : ZMod p).val = p - 1
    have hvalone : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt
    calc
      (-1 : ZMod p).val = p - (1 : ZMod p).val := by
        have h := ZMod.neg_val (1 : ZMod p)
        rw [if_neg (one_ne_zero : (1 : ZMod p) ≠ 0)] at h
        exact h
      _ = p - 1 := by rw [hvalone]
  have hvalNeg : a = -1 ↔ (a : ZMod p).val = p - 1 := by
    constructor
    · rintro rfl
      exact hmOne
    · intro h
      apply Units.ext
      exact ZMod.val_injective p (h.trans hmOne.symm)
  have hone : (1 : G p K) = (σ p K a)⁻¹ ↔ (a : ZMod p).val = 1 := by
    rw [hσinv, ← hσone, (σ_bijective p K).injective.eq_iff]
    simpa only [eq_comm, inv_eq_one] using hvalOne
  have hneg : ι p K = (σ p K a)⁻¹ ↔ (a : ZMod p).val = p - 1 := by
    rw [ι, hσinv, (σ_bijective p K).injective.eq_iff]
    have he : (-1 : (ZMod p)ˣ) = a⁻¹ ↔ a = -1 := by
      constructor
      · intro h
        have hh := congrArg Inv.inv h
        simpa using hh.symm
      · rintro rfl
        simp
    exact he.trans hvalNeg
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, hone, hneg]

lemma θminus_small_three (hp3 : p = 3) :
    θminus p K 1 = -(MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1) := by
  subst p
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  obtain ⟨a, ha⟩ := (σ_bijective 3 K).surjective g⁻¹
  have hg : g = (σ 3 K a)⁻¹ := by rw [ha]; simp
  rw [hg]
  simp only [θminus_coeff, MonoidAlgebra.coeff_neg, Finsupp.neg_apply, minus_basis_coeff]
  have hpos : 0 < (a : ZMod 3).val := ZMod.val_pos.mpr (Units.ne_zero a)
  have hlt : (a : ZMod 3).val < 3 := ZMod.val_lt _
  have hneg : ((-a : (ZMod 3)ˣ) : ZMod 3).val = 3 - (a : ZMod 3).val := by
    rw [Units.val_neg, ZMod.neg_val, if_neg (Units.ne_zero a)]
  rw [hneg]
  interval_cases hval : (a : ZMod 3).val <;> norm_num

lemma θminus_small_five (hp5 : p = 5) :
    θminus p K 1 + θminus p K 2 =
      (-2 : ℤ) • (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1) := by
  subst p
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  obtain ⟨a, ha⟩ := (σ_bijective 5 K).surjective g⁻¹
  have hg : g = (σ 5 K a)⁻¹ := by rw [ha]; simp
  rw [hg]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, θminus_coeff,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, minus_basis_coeff, smul_eq_mul]
  have hpos : 0 < (a : ZMod 5).val := ZMod.val_pos.mpr (Units.ne_zero a)
  have hlt : (a : ZMod 5).val < 5 := ZMod.val_lt _
  have hneg : ((-a : (ZMod 5)ˣ) : ZMod 5).val = 5 - (a : ZMod 5).val := by
    rw [Units.val_neg, ZMod.neg_val, if_neg (Units.ne_zero a)]
  rw [hneg]
  interval_cases hval : (a : ZMod 5).val <;> norm_num

lemma θminus_small_seven (hp7 : p = 7) :
    θminus p K 2 + θminus p K 3 =
      (-2 : ℤ) • (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1) := by
  subst p
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  obtain ⟨a, ha⟩ := (σ_bijective 7 K).surjective g⁻¹
  have hg : g = (σ 7 K a)⁻¹ := by rw [ha]; simp
  rw [hg]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, θminus_coeff,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, minus_basis_coeff, smul_eq_mul]
  have hpos : 0 < (a : ZMod 7).val := ZMod.val_pos.mpr (Units.ne_zero a)
  have hlt : (a : ZMod 7).val < 7 := ZMod.val_lt _
  have hneg : ((-a : (ZMod 7)ˣ) : ZMod 7).val = 7 - (a : ZMod 7).val := by
    rw [Units.val_neg, ZMod.neg_val, if_neg (Units.ne_zero a)]
  rw [hneg]
  interval_cases hval : (a : ZMod 7).val <;> norm_num

end Catalan
