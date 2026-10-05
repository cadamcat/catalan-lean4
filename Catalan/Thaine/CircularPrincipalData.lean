module

public import Catalan.Thaine.AuxiliaryLocalExponent
public import Catalan.Thaine.InvariantPrincipal

/-!
# `Catalan.Thaine.CircularPrincipalData`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma exists_circular_invariant_principal_data
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) :
    ∃ alpha : 𝓞 (A3.Bsub p ell), alpha ≠ 0 ∧
      (∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
        Ideal.map (A3.integralAut sigma).toRingHom (Ideal.span {alpha}) = Ideal.span {alpha}) ∧
      ∀ (v : HeightOneSpectrum (𝓞 (A3.F p)))
        (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))),
        P.asIdeal.LiesOver v.asIdeal → (ell : 𝓞 (A3.F p)) ∈ v.asIdeal →
        ∀ red : 𝓞 (A3.F p) →+* ZMod ell, Function.Surjective red → RingHom.ker red = v.asIdeal →
          red ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) =
            (s : ZMod ell) ^ multiplicity P.asIdeal (Ideal.span {alpha}) := by
  obtain ⟨eta, tau, alpha, halpha, htau, _, hgen, heta, _, hres⟩ :=
    exists_circular_hilbert90_data p ell hp2 hpe hell d hd s hs
  refine ⟨alpha, halpha, ?_, ?_⟩
  · exact principal_ideal_fixed_of_cyclic_coboundary (A3.F p) (A3.Bsub p ell)
      tau hgen eta alpha heta
  · intro v P hOver hellv red hsurj hker
    have circularLocalPrimeOver : P.asIdeal.LiesOver v.asIdeal := hOver
    obtain ⟨redB, _, hkerB, hcomp, hformula⟩ :=
      exists_auxiliary_residue_hom_with_multiplicity p ell hpe v P hellv red hsurj hker
    have hellP : (ell : 𝓞 (A3.Bsub p ell)) ∈ P.asIdeal := by
      simpa only [map_natCast] using (Ideal.mem_of_liesOver P.asIdeal v.asIdeal _).mp hellv
    have hmem := hres P.asIdeal inferInstance hellP
    have hzero : redB ((eta : 𝓞 (A3.Bsub p ell)) -
        algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell))
          ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p))) = 0 := by
      change _ ∈ RingHom.ker redB
      rwa [hkerB]
    have hzero' : redB (eta : 𝓞 (A3.Bsub p ell)) -
        redB (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell))
          ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p))) = 0 := by
      calc
        _ = redB ((eta : 𝓞 (A3.Bsub p ell)) -
            algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell))
              ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p))) :=
          (map_sub redB _ _).symm
        _ = 0 := hzero
    rw [hcomp] at hzero'
    have hetaD : redB (eta : 𝓞 (A3.Bsub p ell)) =
        red ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) :=
      sub_eq_zero.mp hzero'
    rw [← hetaD]
    exact hformula tau s htau alpha eta halpha heta

end Catalan.Thaine
