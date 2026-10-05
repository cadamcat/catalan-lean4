module

public import Catalan.Cassels.CoefficientBounds
public import Catalan.Cassels.TaylorBound
public import Catalan.Cassels.RootCorrection
public import Catalan.Cassels.RemainderArithmetic

/-!
# `Catalan.Cassels.Remainder`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators

namespace Catalan

/-- The finite Taylor estimate with its coefficient premises discharged. -/
lemma cassels_power_taylor_bound
    (p q m : ℕ) (hq0 : 0 < q) (hm : 1 ≤ m)
    (hlo : (m : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ))
    (hhi : (p : ℝ) / (q : ℝ) ≤ (m : ℝ))
    (t : ℝ) (ht : |t| < 1) :
    |Real.rpow (1 + t) ((p : ℝ) / (q : ℝ)) - casselsTaylor p q m t| ≤
      |t| ^ (m + 1) / (((m : ℝ) + 1) * (1 - |t|) ^ 2) := by
  exact cassels_power_taylor_bound_of_coeff p q m hq0 hm hlo hhi
    (fun k => casselsCoeff_real_eq p q k hq0)
    (cassels_coeff_cutoff_bound p q m hq0 hm hlo hhi) t ht

/-- The uniform Cassels remainder bound, with the original signature.
Both signs of t and both endpoints of the closed half interval are included. -/
lemma cassels_remainder_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (t : ℝ) (ht : |t| ≤ (1 : ℝ) / 2) :
    |casselsF p q t - casselsTaylor p q (casselsIndex p q) t| ≤
      |t| ^ (casselsIndex p q + 1) / (1 - |t|) ^ 2 := by
  obtain ⟨hq3, hpodd, hm2, hmp, hlo, hhi⟩ :=
    cassels_index_bounds p q hp hq hp2 hq2 hqp
  have ht1 : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  exact cassels_remainder_of_bounds p q (casselsIndex p q) hq3 hm2 t ht1
    (cassels_power_taylor_bound p q (casselsIndex p q) hq.pos (by omega)
      hlo hhi.le t ht1)
    (cassels_root_correction_bound p q (casselsIndex p q) hpodd hq.pos
      hmp hlo t ht)

#print axioms cassels_power_taylor_bound
#print axioms cassels_remainder_bound

end Catalan
