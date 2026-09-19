import Catalan.Thaine.AuxiliaryRamification
import Catalan.Thaine.ResidueExtension

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma exists_auxiliary_residue_hom
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))) [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal)
    (red : 𝓞 (A3.F p) →+* ZMod ell) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v.asIdeal) :
    ∃ redB : 𝓞 (A3.Bsub p ell) →+* ZMod ell,
      Function.Surjective redB ∧ RingHom.ker redB = P.asIdeal ∧
      (∀ x : 𝓞 (A3.F p), redB (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) x) = red x) ∧
      (∀ (sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell) (x : 𝓞 (A3.Bsub p ell)),
        redB (A3.integralAut sigma x) = redB x) ∧
      ∀ s : (ZMod ell)ˣ, redB (auxiliaryUniformizerRatio p ell s) = (s : ZMod ell) := by
  obtain ⟨hf, _, _, hinertia⟩ := auxiliary_prime_fiber p ell hpe v P hellv
  obtain ⟨redB, hsurjB, hkerB, hcomp⟩ := exists_residue_extension_of_inertia_one
    (A3.F p) (A3.Bsub p ell) (ZMod ell) v P hf red hsurj hker
  refine ⟨redB, hsurjB, hkerB, hcomp, ?_, ?_⟩
  · intro sigma x
    have hmem : A3.integralAut sigma x - x ∈ RingHom.ker redB := by
      rw [hkerB]
      exact (hinertia sigma).2 x
    have hzero : redB (A3.integralAut sigma x - x) = 0 := hmem
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  · intro s
    have hellP : (ell : 𝓞 (A3.Bsub p ell)) ∈ P.asIdeal := by
      simpa only [map_natCast] using (Ideal.mem_of_liesOver P.asIdeal v.asIdeal _).mp hellv
    have hres := (auxiliaryUniformizerRatio_residue p ell s P hellP).2
    have hmem : auxiliaryUniformizerRatio p ell s - ((s : ZMod ell).val : 𝓞 (A3.Bsub p ell)) ∈
        P.asIdeal := by
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simpa only [map_natCast] using hres
    have hzero : redB (auxiliaryUniformizerRatio p ell s -
        ((s : ZMod ell).val : 𝓞 (A3.Bsub p ell))) = 0 := by
      change auxiliaryUniformizerRatio p ell s -
        ((s : ZMod ell).val : 𝓞 (A3.Bsub p ell)) ∈ RingHom.ker redB
      rw [hkerB]
      exact hmem
    exact sub_eq_zero.mp (by
      simpa only [map_sub, map_natCast, ZMod.natCast_zmod_val] using hzero)

end Catalan.Thaine
