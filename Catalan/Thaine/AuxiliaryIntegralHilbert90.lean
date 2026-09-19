import Catalan.Thaine.AuxiliaryGenerator
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma auxiliary_integral_hilbert90
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s)
    (eta : (𝓞 (A3.Bsub p ell))ˣ)
    (hN : Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1) :
    ∃ tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
      tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val ∧
      orderOf tau = ell - 1 ∧
      (∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
        sigma ∈ Subgroup.zpowers tau) ∧
      ∃ alpha : 𝓞 (A3.Bsub p ell), alpha ≠ 0 ∧
        A3.integralAut tau alpha = (eta : 𝓞 (A3.Bsub p ell)) * alpha := by
  obtain ⟨_, tau, hroot, horder, hgen⟩ := auxiliary_cyclic_generator p ell hpe s hs
  have instIntegralHilbertGalois : IsGalois (A3.F p) (A3.Bsub p ell) :=
    A3.isGalois_Bsub p ell (Fact.out : ell.Prime).pos
  have instIntegralHilbertCyclic : IsCyclic (A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨tau, (Subgroup.zpowers tau).eq_top_iff'.mpr hgen⟩
  have hNinv : Algebra.norm (A3.F p)
      (algebraMap (𝓞 (A3.Bsub p ell)) (A3.Bsub p ell)
        ((eta⁻¹ : (𝓞 (A3.Bsub p ell))ˣ) : 𝓞 (A3.Bsub p ell))) = 1 := by
    simp only [map_units_inv, Algebra.norm_inv, hN, inv_one]
  obtain ⟨alpha, halpha, heq⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one
    (A := 𝓞 (A3.F p)) (B := 𝓞 (A3.Bsub p ell)) (K := A3.F p) (L := A3.Bsub p ell)
    hgen hNinv
  refine ⟨tau, hroot, horder, hgen, alpha, halpha, ?_⟩
  have hres : galRestrict (𝓞 (A3.F p)) (A3.F p) (A3.Bsub p ell)
      (𝓞 (A3.Bsub p ell)) tau alpha = A3.integralAut tau alpha := by
    apply RingOfIntegers.ext
    exact algebraMap_galRestrict_apply (𝓞 (A3.F p)) tau alpha
  rw [hres] at heq
  have hmul := congrArg (fun z : 𝓞 (A3.Bsub p ell) => (eta : 𝓞 (A3.Bsub p ell)) * z) heq
  simpa only [← mul_assoc, Units.mul_inv, one_mul] using hmul

end Catalan.Thaine
