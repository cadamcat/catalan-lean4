import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Data.ZMod.Basic

namespace Catalan.Stickelberger

/-- The order of `ell` in `ZMod (ell ^ f - 1)` is exactly `f`. -/
theorem orderOf_natCast_pow_sub_one (ell f : ℕ) (hell : 1 < ell) (hf : 0 < f) :
    orderOf ((ell : ZMod (ell ^ f - 1))) = f := by
  let m := ell ^ f - 1
  have hpow : ((ell : ZMod m) ^ f) = 1 := by
    calc
      ((ell : ZMod m) ^ f) = ((ell ^ f : ℕ) : ZMod m) := by
        rw [Nat.cast_pow]
      _ = (((ell ^ f - 1) + 1 : ℕ) : ZMod m) := by
        congr 1
        exact (Nat.sub_add_cancel (Nat.one_le_pow f ell (Nat.zero_lt_of_lt hell))).symm
      _ = 1 := by
        rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  rw [show ell ^ f - 1 = m from rfl]
  refine (orderOf_eq_iff hf).2 ⟨hpow, ?_⟩
  intro j hj hjpos
  by_cases hfone : f = 1
  · omega
  have hf2 : 2 ≤ f := by omega
  have hpredpos : 0 < f - 1 := by omega
  have hAgt : 1 < ell ^ (f - 1) := Nat.one_lt_pow (by omega) hell
  have hAlt : ell ^ (f - 1) + 1 < ell ^ f := by
    calc
      ell ^ (f - 1) + 1 < ell ^ (f - 1) + ell ^ (f - 1) := by omega
      _ = ell ^ (f - 1) * 2 := by rw [Nat.mul_two]
      _ ≤ ell ^ (f - 1) * ell := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ = ell ^ f := by
        rw [← Nat.pow_succ]
        congr 1
        omega
  have hjpred : j ≤ f - 1 := Nat.le_pred_of_lt hj
  have hAjle : ell ^ j ≤ ell ^ (f - 1) :=
    Nat.pow_le_pow_right (Nat.zero_lt_of_lt hell) hjpred
  have hAjlt : ell ^ j + 1 < ell ^ f :=
    (Nat.add_le_add_right hAjle 1).trans_lt hAlt
  have hjlt : ell ^ j < m := by
    dsimp [m]
    exact Nat.lt_sub_iff_add_lt.mpr hAjlt
  have hmgt : 1 < m := by
    dsimp [m]
    apply Nat.lt_sub_iff_add_lt.mpr
    have : 2 < ell ^ f := by omega
    omega
  have : Fact (1 < m) := ⟨hmgt⟩
  intro hpowj
  have hpowj' : ((ell ^ j : ℕ) : ZMod m) = 1 := by
    simpa only [Nat.cast_pow] using hpowj
  have hval := congrArg ZMod.val hpowj'
  rw [ZMod.val_natCast_of_lt hjlt, ZMod.val_one] at hval
  exact (Nat.ne_of_gt (Nat.one_lt_pow (Nat.ne_of_gt hjpos) hell)) hval

/-- For the cyclotomic field of conductor `ell * (ell ^ f - 1)`, the residue field at a
prime above `ell` has exactly `ell ^ f` elements. -/
theorem card_residue_of_cyclotomic (ell f m n : ℕ) [Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ell : ℤ)})]
    [IsCyclotomicExtension {n} ℚ K]
    (hell : 2 < ell) (hf : 0 < f) (hm : m = ell ^ f - 1) (hn : n = ell * m) :
    Nat.card (NumberField.RingOfIntegers K ⧸ P) = ell ^ f := by
  have hdivpow : ell ∣ ell ^ f := by
    exact dvd_pow_self ell (Nat.ne_of_gt hf)
  have hnotdvd : ¬ ell ∣ m := by
    intro h
    rw [hm] at h
    have hone : ell ∣ 1 := by
      have hpowpos : 0 < ell ^ f := Nat.pow_pos (by omega)
      have hsub : ell ^ f - (ell ^ f - 1) = 1 := by omega
      simpa [hsub] using (Nat.dvd_sub hdivpow h)
    have : ell = 1 := Nat.dvd_one.mp hone
    omega
  have hn' : n = ell ^ (0 + 1) * m := by
    simpa [pow_one] using hn
  have hin : P.inertiaDeg ℤ = orderOf ((ell : ZMod m)) :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq n (m := m) (p := ell) (k := 0) K P hn' hnotdvd
  have hnorm : ell ^ P.inertiaDeg ℤ = Ideal.absNorm P :=
    Ideal.pow_inertiaDeg ell P
  have habs : ell ^ f = Ideal.absNorm P := by
    have horder : orderOf ((ell : ZMod m)) = f := by
      rw [hm]
      exact orderOf_natCast_pow_sub_one ell f (by omega) hf
    rw [hin] at hnorm
    rw [horder] at hnorm
    exact hnorm
  have hcard : Ideal.absNorm P = Nat.card (NumberField.RingOfIntegers K ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hcard.symm.trans habs.symm

end Catalan.Stickelberger
