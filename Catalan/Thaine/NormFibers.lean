module

public import Catalan.Thaine.NormMultiplicity
public import Catalan.Thaine.InvariantFiber

/-!
# `Catalan.Thaine.NormFibers`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma multiplicity_relNorm_eq_degree_mul_of_unramified
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (hIinv : ∀ sigma : L ≃ₐ[F] L,
      Ideal.map (A3.integralAut sigma).toRingHom I = I)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal]
    (hram : ∀ Q : v.asIdeal.primesOver (𝓞 L), Q.1.ramificationIdx (𝓞 F) = 1) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 F) I) =
      Module.finrank F L * multiplicity P.asIdeal I := by
  classical
  let normFiberFintype : Fintype (v.asIdeal.primesOver (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver v.asIdeal).fintype
  have hsum : (∑ Q : v.asIdeal.primesOver (𝓞 L), Q.1.inertiaDeg (𝓞 F)) =
      Module.finrank F L := by
    have h := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L) (G := L ≃ₐ[F] L)
    simpa only [hram, one_mul, IsGalois.card_aut_eq_finrank] using h
  have hm (Q : v.asIdeal.primesOver (𝓞 L)) :
      multiplicity Q.1 I = multiplicity P.asIdeal I := by
    let Qh : HeightOneSpectrum (𝓞 L) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩
    have normFiberPrimeOver : Qh.asIdeal.LiesOver v.asIdeal := Q.2.2
    exact (multiplicity_eq_of_invariant_same_fiber F L I hIinv v P Qh).symm
  rw [multiplicity_relNorm_eq_finsum F L I hI v, finsum_eq_sum_of_fintype]
  simp_rw [hm]
  rw [← Finset.sum_mul, hsum]

lemma multiplicity_relNorm_eq_of_unique_inertia_one
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal]
    (hf : P.asIdeal.inertiaDeg (𝓞 F) = 1)
    (huniq : ∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver v.asIdeal → Q = P) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 F) I) = multiplicity P.asIdeal I := by
  let P' : v.asIdeal.primesOver (𝓞 L) := Ideal.primesOver.mk v.asIdeal P.asIdeal
  have hQeq (Q : v.asIdeal.primesOver (𝓞 L)) : Q = P' := by
    let Qh : HeightOneSpectrum (𝓞 L) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal (huniq Qh Q.2.2))
  rw [multiplicity_relNorm_eq_finsum F L I hI v,
    finsum_eq_single _ P' (fun Q hne => (hne (hQeq Q)).elim)]
  change P.asIdeal.inertiaDeg (𝓞 F) * multiplicity P.asIdeal I = _
  rw [hf, one_mul]

end Catalan.Thaine
