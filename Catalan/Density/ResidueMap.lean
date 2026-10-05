module

public import Mathlib

/-!
# `Catalan.Density.ResidueMap`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma exists_residueHom_to_zmod
    (R : Type*) [CommRing R] (I : Ideal R) (ell : ℕ) (hell : ell.Prime)
    (hcard : Nat.card (R ⧸ I) = ell) :
    ∃ rho : R →+* ZMod ell, Function.Surjective rho ∧ RingHom.ker rho = I := by
  have hcard0 : Nat.card (R ⧸ I) ≠ 0 := by
    rw [hcard]
    exact hell.ne_zero
  let instFiniteQuotient : Finite (R ⧸ I) := Nat.finite_of_card_ne_zero hcard0
  let instFintypeQuotient : Fintype (R ⧸ I) := Fintype.ofFinite (R ⧸ I)
  have hFcard : Fintype.card (R ⧸ I) = ell := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let e : ZMod ell ≃+* (R ⧸ I) :=
    ZMod.ringEquivOfPrime (R ⧸ I) hell hFcard
  let rho : R →+* ZMod ell := e.symm.toRingHom.comp (Ideal.Quotient.mk I)
  refine ⟨rho, ?_, ?_⟩
  · intro z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e z)
    refine ⟨r, ?_⟩
    change e.symm (Ideal.Quotient.mk I r) = z
    rw [hr]
    exact e.symm_apply_apply z
  · apply le_antisymm
    · intro r hr
      change rho r = 0 at hr
      have hzero : Ideal.Quotient.mk I r = 0 := by
        apply e.symm.injective
        change e.symm.toRingHom (Ideal.Quotient.mk I r) = e.symm.toRingHom 0
        simpa only [rho, RingHom.coe_comp, Function.comp_apply, map_zero] using hr
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    · intro r hr
      change rho r = 0
      change e.symm (Ideal.Quotient.mk I r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact e.symm.map_zero

end Catalan.A3
