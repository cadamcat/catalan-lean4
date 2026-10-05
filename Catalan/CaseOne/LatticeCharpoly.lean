module

public import Mathlib

/-!
# `Catalan.CaseOne.LatticeCharpoly`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitLog

lemma charpoly_eq_map_of_lattice_intertwining
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (f : L →ₗ[ℤ] L) (g : E →ₗ[ℝ] E)
    (hfg : ∀ x : L, g (x : E) = (f x : E)) :
    g.charpoly = f.charpoly.map (Int.castRingHom ℝ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  have hmatrix : LinearMap.toMatrix bR bR g =
      (LinearMap.toMatrix b b f).map (Int.castRingHom ℝ) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
    change (b.ofZLatticeBasis ℝ L).repr (g ((b.ofZLatticeBasis ℝ L) j)) i =
      (b.repr (f (b j)) i : ℝ)
    rw [Module.Basis.ofZLatticeBasis_apply, hfg, Module.Basis.ofZLatticeBasis_repr_apply]
  rw [← LinearMap.charpoly_toMatrix g bR, hmatrix, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix f b]

end Catalan.UnitLog
