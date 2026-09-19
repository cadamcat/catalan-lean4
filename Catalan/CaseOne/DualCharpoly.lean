import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma dual_charpoly_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (T : V →ₗ[k] V) :
    (Module.Dual.transpose (R := k) T).charpoly = T.charpoly := by
  classical
  let b := Module.finBasis k V
  rw [← LinearMap.charpoly_toMatrix (Module.Dual.transpose (R := k) T) b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose,
    LinearMap.charpoly_toMatrix]

lemma representation_dual_charpoly {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    (ρ.dual g).charpoly = (ρ g⁻¹).charpoly := by
  rw [Representation.dual_apply, dual_charpoly_eq]

end Catalan.UnitReduction
