module

public import Catalan.Stickelberger.CharacterCircle
public import Catalan.Stickelberger.DirichletTail
public import Catalan.Stickelberger.CharacterContinuity
public import Catalan.Stickelberger.CharacterArgument
public import Catalan.Stickelberger.CharacterZeroBridge

/-!
# `Catalan.Stickelberger.CharacterSpecialValue`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open Filter
open scoped BigOperators Topology
namespace Catalan

lemma tendsto_expZeta_one_partial_sums
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) / (n : ℂ))
      atTop (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) :=
  tendsto_expZeta_one_partial_sums_of_tail_bound unit_circle_dirichlet_tail_bound t ht

lemma expZeta_one_eq_neg_log
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.expZeta (t : UnitAddCircle) 1 =
      -Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
  have hlog := tendsto_unit_circle_log_partial_sums
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
    (exp_two_pi_norm t) (exp_two_pi_ne_one t ht)
  simp_rw [exp_two_pi_pow] at hlog
  exact tendsto_nhds_unique (tendsto_expZeta_one_partial_sums t ht) hlog

lemma sinZeta_one_eq_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.sinZeta (t : UnitAddCircle) 1 =
      (Real.pi : ℂ) * ((1 / 2 : ℂ) - (t : ℂ)) := by
  have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hneg : ((1 - t : ℝ) : UnitAddCircle) = -(t : UnitAddCircle) := by
    rw [AddCircle.coe_sub, show ((1 : ℝ) : UnitAddCircle) = 0 from AddCircle.coe_period (1 : ℝ)]
    exact zero_sub _
  rw [HurwitzZeta.sinZeta_eq, ← hneg, expZeta_one_eq_neg_log t ht,
    expZeta_one_eq_neg_log (1 - t) ht', sub_neg_eq_add,
    log_one_sub_exp_two_pi_difference t ht]
  have h2i : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact mul_div_cancel_left₀ _ h2i

lemma hurwitzZeta_apply_zero_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 =
      (1 / 2 : ℂ) - (t : ℂ) := by
  rw [hurwitzZeta_zero_eq_sine_value_of_mem_Ioo t ht, sinZeta_one_eq_of_mem_Ioo t ht]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

lemma LFunction_zero_eq_neg_weighted_sum
    (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 =
      -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) :=
  LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero hurwitzZeta_apply_zero_of_mem_Ioo p χ hχ

lemma odd_character_weighted_sum_ne_zero
    (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (hodd : χ.Odd) :
    (∑ a : ZMod p, (a.val : ℂ) * χ a) ≠ 0 :=
  odd_character_weighted_sum_ne_zero_of_hurwitz_zero hurwitzZeta_apply_zero_of_mem_Ioo p χ hχ hodd

end Catalan
