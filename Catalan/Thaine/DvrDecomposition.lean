import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma irreducible_of_addVal_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (pi : R) (hpi : IsDiscreteValuationRing.addVal R pi = 1) : Irreducible pi := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖval : IsDiscreteValuationRing.addVal R ϖ = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hϖ
  have hassoc : Associated pi ϖ :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated pi ϖ).mp (hpi.trans hϖval.symm)
  exact hassoc.symm.irreducible hϖ

lemma exists_unit_decomposition_of_addVal_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (pi alpha : R) (hpi : IsDiscreteValuationRing.addVal R pi = 1) (halpha : alpha ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), alpha = (u : R) * pi ^ n ∧
      IsDiscreteValuationRing.addVal R alpha = (n : ℕ∞) := by
  have hpiirr : Irreducible pi := irreducible_of_addVal_one R pi hpi
  obtain ⟨n, u, hdecomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible halpha hpiirr
  refine ⟨n, u, hdecomp, ?_⟩
  exact IsDiscreteValuationRing.addVal_def alpha u hpiirr n hdecomp

end Catalan.Thaine
