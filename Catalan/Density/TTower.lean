import Catalan.Density.HRelative
import Catalan.Density.MCentralizer

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

private theorem inclusion_T_coe {k L : Type*} [Field k] [Field L] [Algebra k L]
    {E D : IntermediateField k L} (h : E ≤ D) (b : E) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ((algebraMap E D b : D) : L) = (b : L) := rfl

private theorem inclusion_T_scalarTower {k L : Type*} [Field k] [Field L] [Algebra k L]
    {E D : IntermediateField k L} (h : E ≤ D) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    IsScalarTower E D L := by
  let instInclusion : Algebra E D := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

@[instance_reducible]
instance instAlgebraHsubT (p q : ℕ) : Algebra (Hsub p q) (T p q) :=
  (IntermediateField.inclusion (show Hsub p q ≤ Tsub p q from le_sup_left)).toRingHom.toAlgebra

instance instModuleHsubT (p q : ℕ) : Module (Hsub p q) (T p q) :=
  (instAlgebraHsubT p q).toModule

@[instance_reducible]
instance instAlgebraMsubT (p q : ℕ) : Algebra (Msub p q) (T p q) :=
  (IntermediateField.inclusion (show Msub p q ≤ Tsub p q from le_sup_right)).toRingHom.toAlgebra

instance instModuleMsubT (p q : ℕ) : Module (Msub p q) (T p q) :=
  (instAlgebraMsubT p q).toModule

@[instance_reducible]
instance instAlgebraBsubT (p q : ℕ) : Algebra (Bsub p q) (T p q) :=
  (IntermediateField.inclusion (show Bsub p q ≤ Tsub p q from
    (show Bsub p q ≤ Msub p q from le_sup_left).trans le_sup_right)).toRingHom.toAlgebra

instance instModuleBsubT (p q : ℕ) : Module (Bsub p q) (T p q) :=
  (instAlgebraBsubT p q).toModule

instance instScalarTowerFHsubT (p q : ℕ) : IsScalarTower (F p) (Hsub p q) (T p q) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instScalarTowerFMsubT (p q : ℕ) : IsScalarTower (F p) (Msub p q) (T p q) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instScalarTowerFBsubT (p q : ℕ) : IsScalarTower (F p) (Bsub p q) (T p q) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instScalarTowerBsubMsubT (p q : ℕ) : IsScalarTower (Bsub p q) (Msub p q) (T p q) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instScalarTowerHsubTOmega (p q : ℕ) : IsScalarTower (Hsub p q) (T p q) Omega :=
  inclusion_T_scalarTower (show Hsub p q ≤ Tsub p q from le_sup_left)

instance instScalarTowerMsubTOmega (p q : ℕ) : IsScalarTower (Msub p q) (T p q) Omega :=
  inclusion_T_scalarTower (show Msub p q ≤ Tsub p q from le_sup_right)

instance instScalarTowerBsubTOmega (p q : ℕ) : IsScalarTower (Bsub p q) (T p q) Omega :=
  inclusion_T_scalarTower (show Bsub p q ≤ Tsub p q from
    (show Bsub p q ≤ Msub p q from le_sup_left).trans le_sup_right)

lemma algebraMap_Hsub_T_coe (p q : ℕ) (x : Hsub p q) :
    ((algebraMap (Hsub p q) (T p q) x : T p q) : Omega) = (x : Omega) :=
  inclusion_T_coe (show Hsub p q ≤ Tsub p q from le_sup_left) x

lemma algebraMap_Msub_T_coe (p q : ℕ) (x : Msub p q) :
    ((algebraMap (Msub p q) (T p q) x : T p q) : Omega) = (x : Omega) :=
  inclusion_T_coe (show Msub p q ≤ Tsub p q from le_sup_right) x

lemma algebraMap_Bsub_T_coe (p q : ℕ) (x : Bsub p q) :
    ((algebraMap (Bsub p q) (T p q) x : T p q) : Omega) = (x : Omega) :=
  inclusion_T_coe (show Bsub p q ≤ Tsub p q from
    (show Bsub p q ≤ Msub p q from le_sup_left).trans le_sup_right) x

lemma isGalois_Tsub_over_F (p q : ℕ) (hq : 0 < q) : IsGalois (F p) (T p q) := by
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instGaloisM : IsGalois (F p) (Msub p q) := isGalois_Msub p q hq
  have instNormalT : Normal (F p) (T p q) :=
    @IntermediateField.normal_sup (F p) Omega _ _ _ (Hsub p q) (Msub p q)
      instGaloisH.to_normal instGaloisM.to_normal
  exact {}

lemma isGalois_Tsub_over_B (p q : ℕ) (hq : 0 < q) : IsGalois (Bsub p q) (T p q) := by
  have instGaloisT : IsGalois (F p) (T p q) := isGalois_Tsub_over_F p q hq
  exact IsGalois.tower_top_of_isGalois (F p) (Bsub p q) (T p q)

end Catalan.A3
