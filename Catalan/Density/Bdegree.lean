module

public import Catalan.Density.BaseFields

/-!
# `Catalan.Density.Bdegree`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma finrank_B_lt (p q : ℕ) (hq : q.Prime) :
    Module.finrank (F p) (Bsub p q) < q := by
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  have hzint : IsIntegral (F p) (primitiveRoot q) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (primitiveRoot q)).isIntegral.tower_top
  have hroot : Polynomial.aeval (primitiveRoot q) (Polynomial.cyclotomic q (F p)) = 0 := by
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]
    exact (primitiveRoot_spec q hq.pos).isRoot_cyclotomic hq.pos
  have hdiv := minpoly.dvd (F p) (primitiveRoot q) hroot
  have hle := Polynomial.natDegree_le_of_dvd hdiv (Polynomial.cyclotomic_ne_zero q (F p))
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hq] at hle
  change Module.finrank (F p) (IntermediateField.adjoin (F p) {primitiveRoot q}) < q
  rw [IntermediateField.adjoin.finrank hzint]
  exact hle.trans_lt (Nat.sub_lt hq.pos (by decide))

lemma coprime_q_finrank_B (p q : ℕ) (hq : q.Prime) :
    Nat.Coprime q (Module.finrank (F p) (Bsub p q)) := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  have hpos : 0 < Module.finrank (F p) (Bsub p q) := Module.finrank_pos
  exact (Nat.not_le_of_lt (finrank_B_lt p q hq)) (Nat.le_of_dvd hpos hd)

end Catalan.A3
