module

public import Catalan.Thaine.DedekindLocalExponent
public import Catalan.Thaine.AuxiliaryResidueHom

/-!
# `Catalan.Thaine.AuxiliaryLocalExponent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma exists_auxiliary_residue_hom_with_multiplicity
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))) [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal)
    (red : 𝓞 (A3.F p) →+* ZMod ell) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v.asIdeal) :
    ∃ redB : 𝓞 (A3.Bsub p ell) →+* ZMod ell,
      Function.Surjective redB ∧ RingHom.ker redB = P.asIdeal ∧
      (∀ x : 𝓞 (A3.F p), redB (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) x) = red x) ∧
      ∀ (tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell) (s : (ZMod ell)ˣ),
        tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val →
        ∀ (alpha : 𝓞 (A3.Bsub p ell)) (eta : (𝓞 (A3.Bsub p ell))ˣ), alpha ≠ 0 →
          A3.integralAut tau alpha = (eta : 𝓞 (A3.Bsub p ell)) * alpha →
          redB (eta : 𝓞 (A3.Bsub p ell)) =
            (s : ZMod ell) ^ multiplicity P.asIdeal (Ideal.span {alpha}) := by
  obtain ⟨redB, hsurjB, hkerB, hcomp, hinertia, hratio⟩ :=
    exists_auxiliary_residue_hom p ell hpe v P hellv red hsurj hker
  refine ⟨redB, hsurjB, hkerB, hcomp, ?_⟩
  intro tau s htau alpha eta halpha heta
  have hellP : (ell : 𝓞 (A3.Bsub p ell)) ∈ P.asIdeal := by
    simpa only [map_natCast] using (Ideal.mem_of_liesOver P.asIdeal v.asIdeal _).mp hellv
  have hpres := ((auxiliary_prime_fiber p ell hpe v P hellv).2.2.2 tau).1
  have heq := residue_coboundary_eq_pow_multiplicity (𝓞 (A3.Bsub p ell)) (ZMod ell)
    P (A3.integralAut tau) hpres redB hkerB (hinertia tau)
    (auxiliaryUniformizer p ell) (auxiliaryUniformizerRatio p ell s) alpha eta
    (auxiliary_prime_ramification p ell hpe v P hellv).2
    (auxiliaryUniformizerRatio_residue p ell s P hellP).1
    (auxiliaryUniformizer_action p ell tau s htau) halpha heta
  simpa only [hratio] using heq

end Catalan.Thaine
