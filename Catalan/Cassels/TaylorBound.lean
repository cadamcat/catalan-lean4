import Catalan.Cassels.Defs

open scoped BigOperators Topology
open Set

namespace Catalan

lemma hasDerivAt_shifted_rpow_product (α : ℝ) (k : ℕ) (s : ℝ)
    (hs : 0 < 1 + s) :
    HasDerivAt
      (fun x : ℝ => (∏ i ∈ Finset.range k, (α - (i : ℝ))) *
        Real.rpow (1 + x) (α - (k : ℝ)))
      ((∏ i ∈ Finset.range (k + 1), (α - (i : ℝ))) *
        Real.rpow (1 + s) (α - ((k + 1 : ℕ) : ℝ))) s := by
  have h := (((hasDerivAt_id s).const_add 1).rpow_const
    (p := α - (k : ℝ)) (Or.inl (ne_of_gt hs))).const_mul
      (∏ i ∈ Finset.range k, (α - (i : ℝ)))
  simpa only [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one,
    sub_add_eq_sub_sub, Real.rpow_eq_pow, id_eq, one_mul, mul_assoc] using h

lemma iteratedDerivWithin_shifted_rpow (α : ℝ) (k : ℕ) (S : Set ℝ)
    (hS : UniqueDiffOn ℝ S) (hpos : ∀ x ∈ S, 0 < 1 + x)
    (s : ℝ) (hs : s ∈ S) :
    iteratedDerivWithin k (fun x : ℝ => Real.rpow (1 + x) α) S s =
      (∏ i ∈ Finset.range k, (α - (i : ℝ))) *
        Real.rpow (1 + s) (α - (k : ℝ)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun x hx => ih x hx) (ih s hs)]
    exact (hasDerivAt_shifted_rpow_product α k s (hpos s hs)).hasDerivWithinAt.derivWithin
      (hS s hs)

lemma contDiffOn_shifted_rpow (α : ℝ) (n : WithTop ℕ∞) (S : Set ℝ)
    (hpos : ∀ x ∈ S, 0 < 1 + x) :
    ContDiffOn ℝ n (fun x : ℝ => Real.rpow (1 + x) α) S := by
  exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne
    (fun x hx => ne_of_gt (hpos x hx))

lemma taylorWithinEval_eq_casselsTaylor_of_coeff (p q m : ℕ)
    (hformula : ∀ k : ℕ, (casselsCoeff p q k : ℝ) =
      (∏ i ∈ Finset.range k, ((p : ℝ) / (q : ℝ) - (i : ℝ))) /
        (k.factorial : ℝ))
    (S : Set ℝ) (hS : UniqueDiffOn ℝ S)
    (hpos : ∀ x ∈ S, 0 < 1 + x) (hzero : (0 : ℝ) ∈ S) (t : ℝ) :
    taylorWithinEval (fun x : ℝ => Real.rpow (1 + x) ((p : ℝ) / (q : ℝ)))
      m S 0 t = casselsTaylor p q m t := by
  rw [taylor_within_apply, casselsTaylor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_shifted_rpow _ _ S hS hpos 0 hzero, hformula k]
  simp only [sub_zero, add_zero, Real.rpow_eq_pow, Real.one_rpow, mul_one, smul_eq_mul]
  ring

lemma cassels_rpow_le_inv_sq (x b γ : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hbx : b ≤ x)
    (hglo : -2 ≤ γ) (hghi : γ ≤ 0) :
    Real.rpow x γ ≤ 1 / b ^ 2 := by
  calc
    Real.rpow x γ ≤ b ^ γ := Real.rpow_le_rpow_of_nonpos hb hbx hghi
    _ ≤ b ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1 hglo
    _ = 1 / b ^ 2 := by norm_num [Real.rpow_neg hb.le, one_div]

lemma cassels_power_taylor_bound_of_coeff
    (p q m : ℕ) (hq0 : 0 < q) (hm : 1 ≤ m)
    (hlo : (m : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ))
    (hhi : (p : ℝ) / (q : ℝ) ≤ (m : ℝ))
    (hformula : ∀ k : ℕ, (casselsCoeff p q k : ℝ) =
      (∏ i ∈ Finset.range k, ((p : ℝ) / (q : ℝ) - (i : ℝ))) /
        (k.factorial : ℝ))
    (hcoeff : |(casselsCoeff p q (m + 1) : ℝ)| ≤ 1 / ((m : ℝ) + 1))
    (t : ℝ) (ht : |t| < 1) :
    |Real.rpow (1 + t) ((p : ℝ) / (q : ℝ)) - casselsTaylor p q m t| ≤
      |t| ^ (m + 1) / (((m : ℝ) + 1) * (1 - |t|) ^ 2) := by
  clear hq0
  by_cases ht0 : t = 0
  · subst t
    have htaylor0 : casselsTaylor p q m 0 = 1 := by
      rw [casselsTaylor, Finset.sum_eq_single 0]
      · simp [hformula 0]
      · intro k hk hk0
        simp [zero_pow hk0]
      · simp
    simp [htaylor0]
  have h0t : (0 : ℝ) ≠ t := Ne.symm ht0
  have hb : 0 < 1 - |t| := sub_pos.mpr ht
  have hS : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_uIcc h0t
  have hlower : ∀ x ∈ uIcc (0 : ℝ) t, -|t| ≤ x := by
    intro x hx
    exact (le_min (neg_nonpos.mpr (abs_nonneg t)) (neg_abs_le t)).trans hx.1
  have hpos : ∀ x ∈ uIcc (0 : ℝ) t, 0 < 1 + x := by
    intro x hx
    have hxlo := hlower x hx
    linarith
  have hf : ContDiffOn ℝ (m + 1)
      (fun x : ℝ => Real.rpow (1 + x) ((p : ℝ) / (q : ℝ))) (uIcc 0 t) :=
    contDiffOn_shifted_rpow _ _ _ hpos
  have hd : DifferentiableOn ℝ
      (iteratedDerivWithin m
        (fun x : ℝ => Real.rpow (1 + x) ((p : ℝ) / (q : ℝ))) (uIcc 0 t))
      (uIcc 0 t) := by
    apply hf.differentiableOn_iteratedDerivWithin _ hS
    norm_cast
    omega
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange h0t hf.of_succ
    (hd.mono Ioo_subset_Icc_self)
  have hxS : x ∈ uIcc (0 : ℝ) t := ⟨hx.1.le, hx.2.le⟩
  rw [taylorWithinEval_eq_casselsTaylor_of_coeff p q m hformula _ hS hpos
    left_mem_uIcc t, iteratedDerivWithin_shifted_rpow _ _ _ hS hpos x hxS] at hrem
  simp only [sub_zero] at hrem
  have hrem' : Real.rpow (1 + t) ((p : ℝ) / (q : ℝ)) - casselsTaylor p q m t =
      (casselsCoeff p q (m + 1) : ℝ) *
        Real.rpow (1 + x) ((p : ℝ) / (q : ℝ) - ((m + 1 : ℕ) : ℝ)) *
        t ^ (m + 1) := by
    rw [hrem, hformula (m + 1)]
    ring
  have hrpow : Real.rpow (1 + x)
      ((p : ℝ) / (q : ℝ) - ((m + 1 : ℕ) : ℝ)) ≤ 1 / (1 - |t|) ^ 2 := by
    apply cassels_rpow_le_inv_sq _ _ _ hb
    · linarith [abs_nonneg t]
    · linarith [hlower x hxS]
    · push_cast
      linarith
    · push_cast
      linarith
  have hrpow0 : 0 ≤ Real.rpow (1 + x)
      ((p : ℝ) / (q : ℝ) - ((m + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (hpos x hxS).le _
  rw [hrem', abs_mul, abs_mul, abs_of_nonneg hrpow0, abs_pow]
  calc
    _ ≤ (1 / ((m : ℝ) + 1)) * (1 / (1 - |t|) ^ 2) * |t| ^ (m + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg t) _)
      exact mul_le_mul hcoeff hrpow hrpow0 (by positivity)
    _ = |t| ^ (m + 1) / (((m : ℝ) + 1) * (1 - |t|) ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end Catalan

#print axioms Catalan.iteratedDerivWithin_shifted_rpow
#print axioms Catalan.taylorWithinEval_eq_casselsTaylor_of_coeff
#print axioms Catalan.cassels_power_taylor_bound_of_coeff
