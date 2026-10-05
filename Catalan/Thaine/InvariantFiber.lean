module

public import Catalan.Thaine.InvariantPrincipal

/-!
# `Catalan.Thaine.InvariantFiber`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma multiplicity_eq_of_invariant_same_fiber
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L]
    (I : Ideal (𝓞 L))
    (hIinv : ∀ sigma : L ≃ₐ[F] L,
      Ideal.map (A3.integralAut sigma).toRingHom I = I)
    (v : HeightOneSpectrum (𝓞 F)) (P Q : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal] [Q.asIdeal.LiesOver v.asIdeal] :
    multiplicity P.asIdeal I = multiplicity Q.asIdeal I := by
  classical
  by_cases hIbot : I = ⊥
  · subst I
    simp
  · let instIdealAction : MulSemiringAction (Gal(L/F)) (Ideal (𝓞 L)) :=
      Ideal.pointwiseMulSemiringAction
    obtain ⟨sigma, hsmul⟩ :=
      Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal P.asIdeal Q.asIdeal (Gal(L/F))
    have hmapP : Ideal.map (A3.integralAut sigma).toRingHom P.asIdeal = Q.asIdeal := by
      rw [Ideal.pointwise_smul_def] at hsmul
      change Ideal.map (MulSemiringAction.toRingHom (Gal(L/F)) (𝓞 L) sigma) P.asIdeal =
        Q.asIdeal at hsmul
      simpa only [show MulSemiringAction.toRingHom (Gal(L/F)) (𝓞 L) sigma =
        (A3.integralAut sigma).toRingHom from rfl] using hsmul
    have hIinv' : Ideal.map (A3.integralAut sigma).toRingHom I = I := hIinv sigma
    have hemult : emultiplicity Q.asIdeal I = emultiplicity P.asIdeal I := by
      calc
        emultiplicity Q.asIdeal I =
            emultiplicity (Ideal.map (A3.integralAut sigma).toRingHom P.asIdeal) I := by
          rw [← hmapP]
        _ = emultiplicity (Ideal.map (A3.integralAut sigma).toRingHom P.asIdeal)
              (Ideal.map (A3.integralAut sigma).toRingHom I) :=
          congrArg (emultiplicity (Ideal.map (A3.integralAut sigma).toRingHom P.asIdeal))
            hIinv'.symm
        _ = emultiplicity P.asIdeal I :=
          Catalan.Stickelberger.emultiplicity_ideal_map (A3.integralAut sigma) P.asIdeal I
    have hfinP : FiniteMultiplicity P.asIdeal I :=
      FiniteMultiplicity.of_prime_left P.prime hIbot
    have hfinQ : FiniteMultiplicity Q.asIdeal I :=
      FiniteMultiplicity.of_prime_left Q.prime hIbot
    apply Nat.cast_injective (R := ℕ∞)
    calc
      (multiplicity P.asIdeal I : ℕ∞) = emultiplicity P.asIdeal I :=
        hfinP.emultiplicity_eq_multiplicity.symm
      _ = emultiplicity Q.asIdeal I := hemult.symm
      _ = (multiplicity Q.asIdeal I : ℕ∞) := hfinQ.emultiplicity_eq_multiplicity

end Catalan.Thaine
