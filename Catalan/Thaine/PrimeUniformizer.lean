module

public import Catalan.Stickelberger.Uniformizer

/-!
# `Catalan.Thaine.PrimeUniformizer`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma prime_root_ramification_uniformizer
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (ell : ℕ) [Fact ell.Prime]
    (hdegree : Module.finrank F L = ell - 1)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 F) ∈ v.asIdeal) (hbase : v.asIdeal.ramificationIdx ℤ = 1)
    (w : L) (hw : IsPrimitiveRoot w ell) :
    P.asIdeal.ramificationIdx (𝓞 F) = ell - 1 ∧
      emultiplicity P.asIdeal (Ideal.span {hw.toInteger - 1}) = 1 := by
  have hp : ell.Prime := Fact.out
  have hell2 : 2 ≤ ell := hp.two_le
  have instPrimeUniformNeEll : NeZero ell := ⟨hp.ne_zero⟩
  have instPrimeUniformFinite : FiniteDimensional F L := inferInstance
  have hellP : (ell : 𝓞 L) ∈ P.asIdeal := by
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver P.asIdeal v.asIdeal (ell : 𝓞 F)).mp hellv
  have hunder : P.asIdeal.under ℤ = Ideal.span {(ell : ℤ)} := by
    symm
    apply Ideal.IsMaximal.eq_of_le inferInstance
      (inferInstance : (P.asIdeal.under ℤ).IsPrime).ne_top
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    change algebraMap ℤ (𝓞 L) (ell : ℤ) ∈ P.asIdeal
    simpa only [map_natCast] using hellP
  have instPrimeUniformOverInt : P.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) := ⟨hunder.symm⟩
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L) (L ≃ₐ[F] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.asIdeal (L ≃ₐ[F] L),
    IsGalois.card_aut_eq_finrank, hdegree] at hfund
  have hediv : P.asIdeal.ramificationIdx (𝓞 F) ∣ ell - 1 := by
    rw [← hfund]
    refine ⟨(v.asIdeal.primesOver (𝓞 L)).ncard * v.asIdeal.inertiaDegIn (𝓞 L), ?_⟩
    ring
  have hele : P.asIdeal.ramificationIdx (𝓞 F) ≤ ell - 1 :=
    Nat.le_of_dvd (by omega) hediv
  have habs : P.asIdeal.ramificationIdx ℤ = P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P.asIdeal, hbase, one_mul]
  have hassoc : Associated ((hw.toInteger - 1) ^ (ell - 1)) (ell : 𝓞 L) :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime ell hw
  have hmem : hw.toInteger - 1 ∈ P.asIdeal := by
    have hpow : (hw.toInteger - 1) ^ (ell - 1) ∈ P.asIdeal := by
      obtain ⟨c, hc⟩ := hassoc.symm.dvd
      rw [hc]
      exact Ideal.mul_mem_right _ _ hellP
    exact (inferInstance : P.asIdeal.IsPrime).mem_of_pow_mem _ hpow
  have hPprime : Prime P.asIdeal := Ideal.prime_of_isPrime P.ne_bot inferInstance
  have hJne : Ideal.span {hw.toInteger - 1} ≠ (0 : Ideal (𝓞 L)) := by
    change Ideal.span {hw.toInteger - 1} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hw.toInteger_isPrimitiveRoot.ne_one hp.one_lt
  have hfin : FiniteMultiplicity P.asIdeal (Ideal.span {hw.toInteger - 1}) :=
    FiniteMultiplicity.of_prime_left hPprime hJne
  have hpos : 0 < multiplicity P.asIdeal (Ideal.span {hw.toInteger - 1}) := by
    exact multiplicity_pos_of_dvd
      (by
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
        exact hmem)
      hfin
  have hspan : (Ideal.span {hw.toInteger - 1}) ^ (ell - 1) =
      Ideal.span {(ell : 𝓞 L)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact hassoc
  have hmult : multiplicity P.asIdeal (Ideal.span {(ell : 𝓞 L)}) =
      P.asIdeal.ramificationIdx ℤ := by
    rw [← Stickelberger.map_span_intCast_eq ell L]
    exact (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (Ideal.span {(ell : ℤ)}) P.asIdeal (by
        rw [Stickelberger.map_span_intCast_eq]
        exact Stickelberger.span_natCast_ne_bot ell L)).symm
  have heq : (ell - 1) * multiplicity P.asIdeal (Ideal.span {hw.toInteger - 1}) =
      P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [← hfin.multiplicity_pow hPprime, hspan, hmult, habs]
  have hnpos : 0 < ell - 1 := by omega
  have hone : multiplicity P.asIdeal (Ideal.span {hw.toInteger - 1}) = 1 := by
    nlinarith
  refine ⟨?_, ?_⟩
  · simpa only [hone, mul_one] using heq.symm
  · rw [hfin.emultiplicity_eq_multiplicity, hone]
    rfl

end Catalan.Thaine
