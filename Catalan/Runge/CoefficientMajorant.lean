module

public import Catalan.Runge.ProductCoefficients

/-!
# `Catalan.Runge.CoefficientMajorant`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace Catalan.Runge

private def risingRat (a : ℚ) (k : ℕ) : ℚ := (-1) ^ k * binomRat (-a) k

private lemma risingRat_eq_prod (a : ℚ) (k : ℕ) :
    risingRat a k = (∏ j ∈ Finset.range k, (a + (j : ℚ))) / (k.factorial : ℚ) := by
  have hfactor (j : ℕ) : -a - (j : ℚ) = (-1 : ℚ) * (a + j) := by ring
  unfold risingRat binomRat
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← mul_div_assoc, ← mul_assoc, ← mul_pow]
  norm_num

private lemma abs_binomRat_le_risingRat (a : ℚ) (ha : 0 ≤ a) (k : ℕ) :
    |binomRat a k| ≤ risingRat a k := by
  rw [binomRat, risingRat_eq_prod, abs_div,
    abs_of_pos (show (0 : ℚ) < k.factorial by positivity), Finset.abs_prod]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.prod_le_prod
  · intro j _
    exact abs_nonneg _
  · intro j _
    apply abs_le.mpr
    have hj : (0 : ℚ) ≤ j := by positivity
    constructor <;> linarith

private lemma risingRat_eq_multichoose (a : ℚ) (k : ℕ) :
    risingRat a k = Ring.multichoose a k := by
  simp only [risingRat, binomRat_eq_choose, Ring.choose_neg', Units.smul_def,
    zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

private lemma risingRat_nat (m k : ℕ) :
    risingRat (m : ℚ) k = (Nat.multichoose m k : ℚ) := by
  rw [risingRat_eq_multichoose]
  have hmap := Ring.map_multichoose (Int.castRingHom ℚ) (m : ℤ) k
  simp only [Int.coe_castRingHom, Int.cast_natCast] at hmap
  rw [← hmap]
  change ((Int.multichoose (m : ℤ) k : ℤ) : ℚ) = (Nat.multichoose m k : ℚ)
  simp [Int.multichoose, Nat.multichoose_eq]

private lemma coeff_prod_pi (ι : Type*) [Fintype ι] (F : ι → PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, F i) =
      ∑ f ∈ Finset.piAntidiag Finset.univ k, ∏ i, PowerSeries.coeff (f i) (F i) := by
  rw [PowerSeries.coeff_prod]
  simp only [Finset.finsuppAntidiag, Finset.sum_map]
  exact Finset.sum_attach (Finset.piAntidiag (Finset.univ : Finset ι) k)
    (fun f : ι → ℕ => ∏ i, PowerSeries.coeff (f i) (F i))

private lemma prod_binomialSeries_neg (ι : Type*) (s : Finset ι) (a : ι → ℚ) :
    (∏ i ∈ s, PowerSeries.binomialSeries ℚ (-a i)) =
      PowerSeries.binomialSeries ℚ (-(∑ i ∈ s, a i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, neg_add,
      PowerSeries.binomialSeries_add, ih]

private lemma risingRat_convolution (ι : Type*) [Fintype ι] (a : ι → ℚ)
    (m : ℕ) (hsum : ∑ i, a i = (m : ℚ)) (k : ℕ) :
    (∑ f ∈ Finset.piAntidiag Finset.univ k, ∏ i, risingRat (a i) (f i)) =
      (Nat.multichoose m k : ℚ) := by
  let r (a : ℚ) : PowerSeries ℚ :=
    PowerSeries.rescale (-1) (PowerSeries.binomialSeries ℚ (-a))
  have hr (a : ℚ) (n : ℕ) : PowerSeries.coeff n (r a) = risingRat a n := by
    simp [r, risingRat, binomRat_eq_choose]
  have hseries : (∏ i, r (a i)) = r (m : ℚ) := by
    dsimp only [r]
    rw [← map_prod, prod_binomialSeries_neg, hsum]
  calc
    _ = PowerSeries.coeff k (∏ i, r (a i)) := by
      rw [coeff_prod_pi]
      simp only [hr]
    _ = PowerSeries.coeff k (r (m : ℚ)) := congrArg (PowerSeries.coeff k) hseries
    _ = _ := by rw [hr, risingRat_nat]

lemma norm_binomialProductCoeff_le_multichoose
    (ι : Type*) [Fintype ι] (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i)
    (w : ι → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (m : ℕ) (hsum : ∑ i, a i = (m : ℚ)) (k : ℕ) :
    ‖binomialProductCoeff ι a w k‖ ≤ (Nat.multichoose m k : ℝ) := by
  have hterm (i : ι) (n : ℕ) :
      ‖(binomRat (a i) n : ℂ) * w i ^ n‖ ≤ (risingRat (a i) n : ℝ) := by
    have hc : ‖(binomRat (a i) n : ℂ)‖ ≤ (risingRat (a i) n : ℝ) := by
      rw [Complex.norm_ratCast]
      exact_mod_cast abs_binomRat_le_risingRat (a i) (ha i) n
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖(binomRat (a i) n : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hw i)) (norm_nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hc
  have hconv : (∑ f ∈ Finset.piAntidiag Finset.univ k,
      ∏ i, (risingRat (a i) (f i) : ℝ)) = (Nat.multichoose m k : ℝ) := by
    exact_mod_cast risingRat_convolution ι a m hsum k
  rw [binomialProductCoeff, sum_bounded_eq_piAntidiag k
    (fun f : ι → ℕ => ∏ i, ((binomRat (a i) (f i) : ℂ) * w i ^ f i))]
  calc
    _ ≤ ∑ f ∈ Finset.piAntidiag Finset.univ k,
        ‖∏ i, ((binomRat (a i) (f i) : ℂ) * w i ^ f i)‖ := norm_sum_le _ _
    _ ≤ ∑ f ∈ Finset.piAntidiag Finset.univ k, ∏ i, (risingRat (a i) (f i) : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => hterm i (f i))
    _ = _ := hconv

end Catalan.Runge
