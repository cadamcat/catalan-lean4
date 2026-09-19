import Catalan.Height.Projective
import Catalan.Mihailescu.PositiveProducts

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma prop44_height (x : ℤ) (hp2 : p ≠ 2) (Θ : R p K) :
    logHeight ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) ≤
      (((size p K Θ : ℝ) + |(weight p K Θ : ℝ)|) / 2) *
        Real.log ((|x| : ℝ) + 1) := by
  let P := posPart p K Θ
  let N := negPart p K Θ
  let A : K := ((upow p K (xmζ p K x hp2) P : Kˣ) : K)
  let B : K := ((upow p K (xmζ p K x hp2) N : Kˣ) : K)
  let M : ℕ := (max (size p K P) (size p K N)).toNat
  have hP (τ : G p K) : 0 ≤ P.coeff τ := le_max_right _ _
  have hN (τ : G p K) : 0 ≤ N.coeff τ := le_max_right _ _
  have hbase : 1 ≤ (|x| : ℝ) + 1 := by linarith [abs_nonneg (x : ℝ)]
  have hpart : upow p K (xmζ p K x hp2) Θ =
      upow p K (xmζ p K x hp2) P / upow p K (xmζ p K x hp2) N := by
    calc
      upow p K (xmζ p K x hp2) Θ = upow p K (xmζ p K x hp2) (P - N) :=
        congrArg _ (part_identities p K Θ).1
      _ = _ := by rw [sub_eq_add_neg, upow_add, upow_neg, div_eq_mul_inv]
  have heq : ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) = A / B := by
    simpa only [Units.val_div_eq_div_val, A, B] using
      congrArg (fun u : Kˣ => (u : K)) hpart
  have hA : IsIntegral ℤ A := integral_upow_xmζ_of_nonneg p K x hp2 P hP
  have hB : IsIntegral ℤ B := integral_upow_xmζ_of_nonneg p K x hp2 N hN
  have hbound (w : InfinitePlace K) : max (w A) (w B) ≤ ((|x| : ℝ) + 1) ^ M := by
    apply max_le
    · exact (infinitePlace_upow_xmζ_le p K x hp2 P hP w).trans
        (pow_le_pow_right₀ hbase (Int.toNat_le_toNat (le_max_left _ _)))
    · exact (infinitePlace_upow_xmζ_le p K x hp2 N hN w).trans
        (pow_le_pow_right₀ hbase (Int.toNat_le_toNat (le_max_right _ _)))
  have h := height_projective_integral_le A B (Units.ne_zero _) (Units.ne_zero _)
    hA hB (((|x| : ℝ) + 1) ^ M) (one_le_pow₀ hbase) hbound
  have hM : (M : ℝ) = (max (size p K P) (size p K N) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg
      ((size_nonneg p K P).trans (le_max_left (size p K P) (size p K N))))
  rw [heq]
  calc
    logHeight (A / B) ≤ Real.log (((|x| : ℝ) + 1) ^ M) := h
    _ = (M : ℝ) * Real.log ((|x| : ℝ) + 1) := Real.log_pow _ _
    _ = _ := by rw [hM, max_part_size]

lemma prop47_height (q : ℕ) [Fact q.Prime] (x : ℤ) (hp2 : p ≠ 2)
    (Θ : mihIdeal p K q x hp2) :
    logHeight ((alpha p K q x hp2 Θ : Kˣ) : K) ≤
      (((size p K Θ.val : ℝ) + |(weight p K Θ.val : ℝ)|) / (2 * (q : ℝ))) *
        Real.log ((|x| : ℝ) + 1) := by
  have h := prop44_height p K x hp2 Θ.val
  have hp : ((alpha p K q x hp2 Θ : Kˣ) : K) ^ q =
      ((upow p K (xmζ p K x hp2) Θ.val : Kˣ) : K) := by
    exact congrArg (fun a : Kˣ => (a : K)) (alpha_pow p K q x hp2 Θ)
  rw [← hp, height_pow] at h
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  apply (mul_le_mul_iff_left₀ hq).mp
  calc
    logHeight ((alpha p K q x hp2 Θ : Kˣ) : K) * (q : ℝ) ≤
        (((size p K Θ.val : ℝ) + |(weight p K Θ.val : ℝ)|) / 2) *
          Real.log ((|x| : ℝ) + 1) := by nlinarith
    _ = ((((size p K Θ.val : ℝ) + |(weight p K Θ.val : ℝ)|) /
        (2 * (q : ℝ))) * Real.log ((|x| : ℝ) + 1)) * (q : ℝ) := by
      field_simp [ne_of_gt hq]

end Catalan
