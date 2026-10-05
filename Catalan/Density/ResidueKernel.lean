module

public import Mathlib

/-!
# `Catalan.Density.ResidueKernel`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer

lemma residue_power_iff_of_surjective
    (R S : Type*) [CommRing R] [CommRing S]
    (rho : R →+* S) (hsurj : Function.Surjective rho)
    (I : Ideal R) (hker : RingHom.ker rho = I) (q : ℕ) (u : Rˣ) :
    (∃ v : (R ⧸ I)ˣ, v ^ q = Units.map (Ideal.Quotient.mk I).toMonoidHom u) ↔
      ∃ v : Sˣ, v ^ q = Units.map rho.toMonoidHom u := by
  subst I
  let e : R ⧸ RingHom.ker rho ≃+* S :=
    RingHom.quotientKerEquivOfSurjective hsurj
  have hmk : e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker rho)) = rho := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj r
  have hmk' : e.toMonoidHom.comp (Ideal.Quotient.mk (RingHom.ker rho)).toMonoidHom =
      rho.toMonoidHom := congrArg RingHom.toMonoidHom hmk
  have hsymm : e.symm.toRingHom.comp rho = Ideal.Quotient.mk (RingHom.ker rho) :=
    RingHom.quotientKerEquivOfSurjective_symm_comp hsurj
  have hsymm' : e.symm.toMonoidHom.comp rho.toMonoidHom =
      (Ideal.Quotient.mk (RingHom.ker rho)).toMonoidHom :=
    congrArg RingHom.toMonoidHom hsymm
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Units.map e.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]
    calc
      Units.map e.toMonoidHom
          (Units.map (Ideal.Quotient.mk (RingHom.ker rho)).toMonoidHom u) =
          Units.map (e.toMonoidHom.comp
            (Ideal.Quotient.mk (RingHom.ker rho)).toMonoidHom) u := by
              simp only [Units.map_comp, MonoidHom.comp_apply]
      _ = Units.map rho.toMonoidHom u := by rw [hmk']
  · rintro ⟨v, hv⟩
    refine ⟨Units.map e.symm.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]
    calc
      Units.map e.symm.toMonoidHom (Units.map rho.toMonoidHom u) =
          Units.map (e.symm.toMonoidHom.comp rho.toMonoidHom) u := by
            simp only [Units.map_comp, MonoidHom.comp_apply]
      _ = Units.map (Ideal.Quotient.mk (RingHom.ker rho)).toMonoidHom u := by
        rw [hsymm']

end Catalan.Kummer
