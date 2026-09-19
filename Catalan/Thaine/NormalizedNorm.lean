import Catalan.Thaine.NormalizedPair
import Catalan.Thaine.CyclotomicNorm
import Catalan.Thaine.NormFactor

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma normalizedEpsilon_norm_one
    (F L : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    [IsCyclotomicExtension {ell} F L] (hdegree : Module.finrank F L = ell - 1)
    (hp2 : p ≠ 2) (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (z : F) (hz : IsPrimitiveRoot z p) (a : (ZMod p)ˣ)
    (w : L) (hw : IsPrimitiveRoot w ell) :
    Algebra.norm F (normalizedEpsilon p a (algebraMap F L z) w) = 1 := by
  have hnorm := norm_mixed_epsilon F L ell hdegree w hw z
    (a : ZMod p).val (normalizedHalf p a : ℤ)
  have hfactor := epsilon_norm_factor_eq_one F p ell z hz a (normalizedHalf p a : ℤ)
    (normalizedHalf_root p hp2 a z hz) hell
  simpa only [normalizedEpsilon, zpow_natCast] using hnorm.trans hfactor

lemma normalizedPair_norm_one
    (F L : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    [IsCyclotomicExtension {ell} F L] (hdegree : Module.finrank F L = ell - 1)
    (hp2 : p ≠ 2) (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (z : F) (hz : IsPrimitiveRoot z p) (a : (ZMod p)ˣ)
    (w : L) (hw : IsPrimitiveRoot w ell) :
    Algebra.norm F (normalizedPair p a (algebraMap F L z) w) = 1 := by
  rw [normalizedPair, map_mul,
    normalizedEpsilon_norm_one F L p ell hdegree hp2 hell z hz a w hw,
    normalizedEpsilon_norm_one F L p ell hdegree hp2 hell z hz a w⁻¹ hw.inv, one_mul]

end Catalan.Thaine
