import Catalan.CaseOne.CyclicShift

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitLog

noncomputable def cyclicZeroSum (n : ℕ) [NeZero n] : Submodule ℝ (ZMod n → ℝ) where
  carrier := {f | ∑ i, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∑ i, (f i + g i)) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  smul_mem' := by
    intro c f hf
    change (∑ i, c * f i) = 0
    rw [← Finset.mul_sum, hf, mul_zero]

noncomputable def cyclicZeroSumShift (n : ℕ) [NeZero n] :
    cyclicZeroSum n →ₗ[ℝ] cyclicZeroSum n where
  toFun f := ⟨fun i => f.val (i + 1), by
    change ∑ i, f.val (i + 1) = 0
    exact (Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) f.val).trans f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cyclicZeroSumShift_apply (n : ℕ) [NeZero n] (f : cyclicZeroSum n) (i : ZMod n) :
    (cyclicZeroSumShift n f).val i = f.val (i + 1) := rfl

lemma cyclicZeroSumShift_charpoly (n : ℕ) [NeZero n] :
    (cyclicZeroSumShift n).charpoly =
      ∑ i ∈ Finset.range n, (Polynomial.X : Polynomial ℝ) ^ i := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  let mean : (ZMod n → ℝ) → ℝ := fun f => (∑ i, f i) / (n : ℝ)
  have hmean_sub (f : ZMod n → ℝ) : (fun i => f i - mean f) ∈ cyclicZeroSum n := by
    change (∑ i, (f i - mean f)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    dsimp only [mean]
    field_simp
    ring
  have hmean_pair (x : ℝ × cyclicZeroSum n) :
      mean (fun i => x.1 + x.2.val i) = x.1 := by
    have hx : ∑ i, x.2.val i = 0 := x.2.property
    dsimp only [mean]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, hx, add_zero]
    field_simp
  let e : (ℝ × cyclicZeroSum n) ≃ₗ[ℝ] (ZMod n → ℝ) :=
    { toFun := fun x i => x.1 + x.2.val i
      invFun := fun f => (mean f, ⟨fun i => f i - mean f, hmean_sub f⟩)
      left_inv := by
        intro x
        apply Prod.ext
        · exact hmean_pair x
        · apply Subtype.ext
          funext i
          change x.1 + x.2.val i - mean (fun j => x.1 + x.2.val j) = x.2.val i
          rw [hmean_pair]
          ring
      right_inv := by
        intro f
        funext i
        change mean f + (f i - mean f) = f i
        ring
      map_add' := by
        intro x y
        funext i
        change (x.1 + y.1) + (x.2.val i + y.2.val i) =
          (x.1 + x.2.val i) + (y.1 + y.2.val i)
        ring
      map_smul' := by
        intro c x
        funext i
        change c * x.1 + c * x.2.val i = c * (x.1 + x.2.val i)
        ring }
  let T : (ℝ × cyclicZeroSum n) →ₗ[ℝ] (ℝ × cyclicZeroSum n) :=
    (1 : ℝ →ₗ[ℝ] ℝ).prodMap (cyclicZeroSumShift n)
  have hconj : e.conj T = cyclicShift n := by
    apply LinearMap.ext
    intro f
    obtain ⟨x, rfl⟩ := e.surjective f
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    funext i
    rfl
  have hprod : T.charpoly =
      ((Polynomial.X : Polynomial ℝ) - 1) * (cyclicZeroSumShift n).charpoly := by
    simp only [T, LinearMap.charpoly_prodMap, LinearMap.charpoly_one, Module.finrank_self, pow_one]
  have htotal : ((Polynomial.X : Polynomial ℝ) - 1) * (cyclicZeroSumShift n).charpoly =
      (Polynomial.X : Polynomial ℝ) ^ n - 1 := by
    calc
      _ = T.charpoly := hprod.symm
      _ = (e.conj T).charpoly := (LinearEquiv.charpoly_conj e T).symm
      _ = _ := by rw [hconj, cyclicShift_charpoly]
  have hXne : (Polynomial.X : Polynomial ℝ) - 1 ≠ 0 := by
    simpa only [Polynomial.C_1] using (Polynomial.monic_X_sub_C (1 : ℝ)).ne_zero
  apply mul_left_cancel₀ hXne
  rw [htotal, mul_geom_sum]

end Catalan.UnitLog
