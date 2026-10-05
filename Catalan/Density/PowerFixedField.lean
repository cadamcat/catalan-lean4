module

public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.Density.PowerFixedField`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.FieldTower

lemma exists_intermediateField_of_galois_power_quotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : Type*) [CommGroup A] (e : (L ≃ₐ[K] L) ≃* A) (q : ℕ) :
    ∃ S : IntermediateField K L,
      IsAbelianGalois K S ∧
      (∀ σ : S ≃ₐ[K] S, σ ^ q = 1) ∧
      Nonempty ((S ≃ₐ[K] S) ≃* (A ⧸ Catalan.UnitQuotient.qPowers A q)) := by
  let N : Subgroup (L ≃ₐ[K] L) := (Catalan.UnitQuotient.qPowers A q).comap e.toMonoidHom
  let instNormalN : N.Normal := inferInstance
  let S : IntermediateField K L := IntermediateField.fixedField N
  let instGaloisS : IsGalois K S := inferInstance
  let E : (S ≃ₐ[K] S) ≃* (A ⧸ Catalan.UnitQuotient.qPowers A q) :=
    (IsGalois.normalAutEquivQuotient N).symm.trans
      (QuotientGroup.congr N (Catalan.UnitQuotient.qPowers A q) e
        (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
  have hexponent (x : A ⧸ Catalan.UnitQuotient.qPowers A q) : x ^ q = 1 := by
    induction x using QuotientGroup.induction_on with
    | _ a =>
      change QuotientGroup.mk (a ^ q) = 1
      exact (QuotientGroup.eq_one_iff (a ^ q)).mpr ⟨a, rfl⟩
  refine ⟨S, ?_, ?_, ⟨E⟩⟩
  · exact
      { is_comm.comm := fun σ τ => E.injective (by rw [map_mul, map_mul, mul_comm]) }
  · intro σ
    apply E.injective
    rw [map_pow, map_one]
    exact hexponent (E σ)

end Catalan.FieldTower
