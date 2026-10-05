module

public import Catalan.Density.NormalM
public import Catalan.Density.FiniteM
public import Catalan.Density.UnitRoots

/-!
# `Catalan.Density.KummerTower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

private theorem inclusion_algebraMap_coe {k L : Type*} [Field k] [Field L] [Algebra k L]
    {E D : IntermediateField k L} (h : E ≤ D) (b : E) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ((algebraMap E D b : D) : L) = (b : L) := rfl

@[instance_reducible]
instance instAlgebraBsubMsub (p q : ℕ) : Algebra (Bsub p q) (Msub p q) :=
  (IntermediateField.inclusion (show Bsub p q ≤ Msub p q from le_sup_left)).toRingHom.toAlgebra

instance instModuleBsubMsub (p q : ℕ) : Module (Bsub p q) (Msub p q) :=
  (instAlgebraBsubMsub p q).toModule

instance instScalarTowerFBsubMsub (p q : ℕ) :
    IsScalarTower (F p) (Bsub p q) (Msub p q) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instScalarTowerBsubMsubOmega (p q : ℕ) :
    IsScalarTower (Bsub p q) (Msub p q) Omega :=
  IsScalarTower.of_algebraMap_eq' rfl

lemma algebraMap_Bsub_Msub_coe (p q : ℕ) (b : Bsub p q) :
    ((algebraMap (Bsub p q) (Msub p q) b : Msub p q) : Omega) = (b : Omega) := by
  exact inclusion_algebraMap_coe (show Bsub p q ≤ Msub p q from le_sup_left) b

lemma finiteDimensional_Msub_over_B (p q : ℕ) (hq : 0 < q) :
    FiniteDimensional (Bsub p q) (Msub p q) := by
  have instFiniteM : FiniteDimensional (F p) (Msub p q) := finiteDimensional_Msub p q hq
  exact FiniteDimensional.right (F p) (Bsub p q) (Msub p q)

lemma isGalois_Msub_over_B (p q : ℕ) (hq : 0 < q) :
    IsGalois (Bsub p q) (Msub p q) := by
  have instGaloisM : IsGalois (F p) (Msub p q) := isGalois_Msub p q hq
  exact IsGalois.tower_top_of_isGalois (F p) (Bsub p q) (Msub p q)

end Catalan.A3
