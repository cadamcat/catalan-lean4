import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer

lemma residue_power_map_tower
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : ℕ) (P : Ideal T) (u : Rˣ)
    (hres : ∃ v : (R ⧸ P.under R)ˣ,
      v ^ q = Units.map (Ideal.Quotient.mk (P.under R)).toMonoidHom u) :
    ∃ v : (S ⧸ P.under S)ˣ,
      v ^ q = Units.map (Ideal.Quotient.mk (P.under S)).toMonoidHom
        (Units.map (algebraMap R S).toMonoidHom u) := by
  let instLiesOver : (P.under S).LiesOver (P.under R) := by
    exact Ideal.LiesOver.tower_bot P (P.under S) (P.under R)
  obtain ⟨v, hv⟩ := hres
  have hsq :
      (algebraMap (R ⧸ P.under R) (S ⧸ P.under S)).toMonoidHom.comp
          (Ideal.Quotient.mk (P.under R)).toMonoidHom =
        (Ideal.Quotient.mk (P.under S)).toMonoidHom.comp
          (algebraMap R S).toMonoidHom := by
    ext r
    exact Ideal.Quotient.algebraMap_mk_of_liesOver (P.under S) (P.under R) r
  let vS : (S ⧸ P.under S)ˣ :=
    Units.map (algebraMap (R ⧸ P.under R) (S ⧸ P.under S)).toMonoidHom v
  refine ⟨vS, ?_⟩
  rw [show vS ^ q = Units.map
      (algebraMap (R ⧸ P.under R) (S ⧸ P.under S)).toMonoidHom (v ^ q) by
        rw [map_pow]]
  rw [hv]
  calc
    Units.map (algebraMap (R ⧸ P.under R) (S ⧸ P.under S)).toMonoidHom
        (Units.map (Ideal.Quotient.mk (P.under R)).toMonoidHom u) =
      Units.map ((algebraMap (R ⧸ P.under R) (S ⧸ P.under S)).toMonoidHom.comp
        (Ideal.Quotient.mk (P.under R)).toMonoidHom) u := by
          simp only [Units.map_comp, MonoidHom.comp_apply]
    _ = Units.map ((Ideal.Quotient.mk (P.under S)).toMonoidHom.comp
        (algebraMap R S).toMonoidHom) u := by rw [hsq]
    _ = Units.map (Ideal.Quotient.mk (P.under S)).toMonoidHom
        (Units.map (algebraMap R S).toMonoidHom u) := by
          simp only [Units.map_comp, MonoidHom.comp_apply]

end Catalan.Kummer
