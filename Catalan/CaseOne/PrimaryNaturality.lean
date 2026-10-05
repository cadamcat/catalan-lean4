module

public import Catalan.CaseOne.PrimaryUnits

/-!
# `Catalan.CaseOne.PrimaryNaturality`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitQuotient

lemma primaryUnits_map
    (A B : Type*) [CommRing A] [CommRing B] (q : ℕ) (hq : 0 < q)
    (f : A →+* B) (u : Aˣ) (hu : u ∈ primaryUnits A q) :
    Units.map f.toMonoidHom u ∈ primaryUnits B q := by
  obtain ⟨v, hv⟩ := (mem_primaryUnits_iff A q hq u).mp hu
  apply (mem_primaryUnits_iff B q hq (Units.map f.toMonoidHom u)).mpr
  refine ⟨f v, ?_⟩
  obtain ⟨w, hw⟩ := hv
  refine ⟨f w, ?_⟩
  have huval : ((Units.map f.toMonoidHom u : Bˣ) : B) = f (u : A) := rfl
  rw [huval]
  simpa only [map_sub, map_pow, map_natCast, map_mul] using congrArg f hw

lemma primaryUnits_map_equiv_iff
    (A : Type*) [CommRing A] (q : ℕ) (hq : 0 < q)
    (e : A ≃+* A) (u : Aˣ) :
    Units.map e.toMonoidHom u ∈ primaryUnits A q ↔ u ∈ primaryUnits A q := by
  constructor
  · intro hu
    have hback := primaryUnits_map A A q hq e.symm.toRingHom
      (Units.map e.toMonoidHom u) hu
    have hcomp : Units.map e.symm.toMonoidHom
        (Units.map e.toMonoidHom u) = u := by
      apply Units.ext
      change e.symm (e (u : A)) = (u : A)
      rw [e.symm_apply_apply]
    rw [hcomp] at hback
    exact hback
  · intro hu
    exact primaryUnits_map A A q hq e.toRingHom u hu

end Catalan.UnitQuotient
