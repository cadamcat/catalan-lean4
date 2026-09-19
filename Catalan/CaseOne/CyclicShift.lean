import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitLog

noncomputable def cyclicShift (n : ℕ) [NeZero n] : (ZMod n → ℝ) →ₗ[ℝ] (ZMod n → ℝ) where
  toFun f i := f (i + 1)
  map_add' f g := rfl
  map_smul' c f := rfl

private lemma cyclicShift_pow_apply (n : ℕ) [NeZero n] (k : ℕ)
    (f : ZMod n → ℝ) (i : ZMod n) :
    ((cyclicShift n) ^ k) f i = f (i + (k : ZMod n)) := by
  induction k generalizing f i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [cyclicShift, LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_succ, add_assoc]

private lemma cyclicShift_pow_n (n : ℕ) [NeZero n] : (cyclicShift n) ^ n = 1 := by
  ext f i
  simp [cyclicShift_pow_apply]

private lemma polynomial_eq_zero_of_aeval_shift (n : ℕ) [NeZero n]
    (P : Polynomial ℝ) (hdeg : P.natDegree < n)
    (hz : Polynomial.aeval (cyclicShift n) P = 0) : P = 0 := by
  classical
  let delta : ZMod n → ℝ := fun i => if i = 0 then 1 else 0
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < n
  · have hvalue : (Polynomial.aeval (cyclicShift n) P) delta (-(j : ZMod n)) = P.coeff j := by
      rw [Polynomial.aeval_eq_sum_range' hdeg]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, cyclicShift_pow_apply]
      rw [Finset.sum_eq_single j]
      · simp [delta]
      · intro k hk hkj
        have hne : -(j : ZMod n) + (k : ZMod n) ≠ 0 := by
          intro hzero
          have heq : (k : ZMod n) = (j : ZMod n) := by linear_combination hzero
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hk), ZMod.val_natCast_of_lt hj] at hv
          exact hkj hv
        simp [delta, hne]
      · intro hjnot
        exact (hjnot (Finset.mem_range.mpr hj)).elim
    rw [hz] at hvalue
    simpa only [LinearMap.zero_apply, Pi.zero_apply] using hvalue.symm
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma cyclicShift_charpoly (n : ℕ) [NeZero n] :
    (cyclicShift n).charpoly = (Polynomial.X : Polynomial ℝ) ^ n - 1 := by
  have hdeg : (cyclicShift n).charpoly.natDegree = n := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_fintype_fun_eq_card, ZMod.card]
  have hmono : Polynomial.IsMonicOfDegree (cyclicShift n).charpoly n :=
    ⟨hdeg, LinearMap.charpoly_monic _⟩
  have hXmono : Polynomial.IsMonicOfDegree ((Polynomial.X : Polynomial ℝ) ^ n - 1) n := by
    constructor
    · simpa only [Polynomial.C_1] using
        (Polynomial.natDegree_X_pow_sub_C (n := n) (r := (1 : ℝ)))
    · simpa only [Polynomial.C_1] using Polynomial.monic_X_pow_sub_C (1 : ℝ) (NeZero.ne n)
  have hXzero : Polynomial.aeval (cyclicShift n) ((Polynomial.X : Polynomial ℝ) ^ n - 1) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, cyclicShift_pow_n, sub_self]
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_aeval_shift n _
    (hmono.natDegree_sub_lt (NeZero.ne n) hXmono)
  rw [map_sub, LinearMap.aeval_self_charpoly, hXzero, sub_self]

end Catalan.UnitLog
