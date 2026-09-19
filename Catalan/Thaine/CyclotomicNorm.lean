import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma norm_cyclotomic_sub
    (F L : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (ell : ℕ) [Fact ell.Prime] [IsCyclotomicExtension {ell} F L]
    (hdegree : Module.finrank F L = ell - 1)
    (w : L) (hw : IsPrimitiveRoot w ell) (x : F) :
    Algebra.norm F (algebraMap F L x - w) =
      Polynomial.eval x (Polynomial.cyclotomic ell F) := by
  classical
  have hell : ell.Prime := Fact.out
  let normCyclotomicNeZeroEll : NeZero ell := ⟨hell.ne_zero⟩
  let pb := hw.powerBasis F
  have hgen : pb.gen = w := hw.powerBasis_gen F
  have hint : IsIntegral F w := hgen ▸ pb.isIntegral_gen
  have hdim : (minpoly F w).natDegree = ell - 1 := by
    rw [← hgen, pb.natDegree_minpoly, ← pb.finrank, hdegree]
  have hmin : Polynomial.cyclotomic ell F = minpoly F w := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic ell F)
    · apply minpoly.dvd F w
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact hw.isRoot_cyclotomic hell.pos
    · rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hell, hdim]
  rw [hmin, ← hgen, ← charpoly_leftMulMatrix pb, Matrix.eval_charpoly,
    Algebra.norm_eq_matrix_det pb.basis, map_sub, AlgHom.commutes]
  rfl

lemma norm_mixed_epsilon
    (F L : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (ell : ℕ) [Fact ell.Prime] [IsCyclotomicExtension {ell} F L]
    (hdegree : Module.finrank F L = ell - 1)
    (w : L) (hw : IsPrimitiveRoot w ell) (z : F) (a : ℕ) (m : ℤ) :
    Algebra.norm F ((algebraMap F L z) ^ m *
      ((algebraMap F L z) ^ a - w) / (algebraMap F L z - w)) =
      (z ^ m) ^ (ell - 1) *
        Polynomial.eval (z ^ a) (Polynomial.cyclotomic ell F) /
          Polynomial.eval z (Polynomial.cyclotomic ell F) := by
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [← map_zpow₀, Algebra.norm_algebraMap, hdegree,
    ← map_pow, norm_cyclotomic_sub F L ell hdegree w hw (z ^ a),
    norm_cyclotomic_sub F L ell hdegree w hw z]

end Catalan.Thaine
