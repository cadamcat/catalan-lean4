import Mathlib

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

private lemma distinct_maximal_multiplicity_zero
    {R : Type*} [CommRing R] (A B : Ideal R) [A.IsMaximal] [B.IsMaximal]
    (hne : A ≠ B) : multiplicity A B = 0 := by
  apply multiplicity_eq_zero.mpr
  intro hdiv
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : B.IsMaximal)
    (inferInstance : A.IsMaximal).ne_top (Ideal.le_of_dvd hdiv)).symm

private lemma prime_multiplicity_relNorm_eq_finsum
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (Q : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 F) Q.asIdeal) =
      ∑ᶠ P : v.asIdeal.primesOver (𝓞 L),
        P.1.inertiaDeg (𝓞 F) * multiplicity P.1 Q.asIdeal := by
  classical
  let w : Ideal (𝓞 F) := Q.asIdeal.under (𝓞 F)
  have instNormPrimeUnderMax : w.IsMaximal := inferInstance
  have instNormPrimeUnderOver : Q.asIdeal.LiesOver w := inferInstance
  have hvprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot inferInstance
  have hwne : w ≠ (0 : Ideal (𝓞 F)) := Ideal.under_ne_bot (𝓞 F) Q.ne_bot
  have hnorm : Ideal.relNorm (𝓞 F) Q.asIdeal = w ^ Q.asIdeal.inertiaDeg (𝓞 F) :=
    Ideal.relNorm_eq_pow_of_isMaximal Q.asIdeal w
  by_cases hvw : v.asIdeal = w
  · have instNormPrimeOverV : Q.asIdeal.LiesOver v.asIdeal := ⟨hvw⟩
    let qv : v.asIdeal.primesOver (𝓞 L) := ⟨Q.asIdeal, inferInstance, instNormPrimeOverV⟩
    rw [hnorm, ← hvw, multiplicity_pow_self_of_prime hvprime]
    symm
    calc
      (∑ᶠ P : v.asIdeal.primesOver (𝓞 L),
          P.1.inertiaDeg (𝓞 F) * multiplicity P.1 Q.asIdeal) =
          qv.1.inertiaDeg (𝓞 F) * multiplicity qv.1 Q.asIdeal := by
        apply finsum_eq_single _ qv
        intro P hP
        have instNormPrimeOtherMax : P.1.IsMaximal :=
          Ideal.IsMaximal.of_liesOver_isMaximal P.1 v.asIdeal
        have hPQ : P.1 ≠ Q.asIdeal := by
          intro h
          apply hP
          exact Subtype.ext h
        rw [distinct_maximal_multiplicity_zero P.1 Q.asIdeal hPQ, mul_zero]
      _ = Q.asIdeal.inertiaDeg (𝓞 F) := by simp only [qv, multiplicity_self, mul_one]
  · have hfin : FiniteMultiplicity v.asIdeal w := FiniteMultiplicity.of_prime_left hvprime hwne
    rw [hnorm, hfin.multiplicity_pow hvprime, distinct_maximal_multiplicity_zero v.asIdeal w hvw,
      mul_zero]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro P
    have instNormPrimeAwayMax : P.1.IsMaximal :=
      Ideal.IsMaximal.of_liesOver_isMaximal P.1 v.asIdeal
    have hPQ : P.1 ≠ Q.asIdeal := by
      intro h
      apply hvw
      exact (Ideal.over_def P.1 v.asIdeal).trans (congrArg (Ideal.under (𝓞 F)) h)
    rw [distinct_maximal_multiplicity_zero P.1 Q.asIdeal hPQ, mul_zero]

lemma multiplicity_relNorm_eq_finsum
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 F) I) =
      ∑ᶠ Q : v.asIdeal.primesOver (𝓞 L),
        Q.1.inertiaDeg (𝓞 F) * multiplicity Q.1 I := by
  classical
  let instNormMultiplicityFiberFintype : Fintype (v.asIdeal.primesOver (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver v.asIdeal).fintype
  have hvprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot inferInstance
  have hPprime (P : v.asIdeal.primesOver (𝓞 L)) : Prime P.1 :=
    Ideal.prime_of_isPrime (Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2) inferInstance
  have hnormne (J : Ideal (𝓞 L)) (hJ : J ≠ 0) : Ideal.relNorm (𝓞 F) J ≠ 0 := by
    intro h
    exact hJ (Ideal.relNorm_eq_bot_iff.mp h)
  rw [finsum_eq_sum_of_fintype]
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hI rfl).elim
  | h₂ J hunit =>
    have hJone : J = 1 := isUnit_iff_eq_one.mp hunit
    subst J
    rw [map_one, (FiniteMultiplicity.of_prime_left hvprime one_ne_zero).one_right]
    symm
    apply Finset.sum_eq_zero
    intro P hP
    rw [(FiniteMultiplicity.of_prime_left (hPprime P) one_ne_zero).one_right, mul_zero]
  | h₃ J Q hJ hQ IH =>
    have hQprime : Q.IsPrime := Ideal.isPrime_of_prime hQ
    let q : HeightOneSpectrum (𝓞 L) := ⟨Q, hQprime, hQ.ne_zero⟩
    have hprime := prime_multiplicity_relNorm_eq_finsum F L q v
    simp only [finsum_eq_sum_of_fintype] at hprime
    have hfinNorm : FiniteMultiplicity v.asIdeal
        (Ideal.relNorm (𝓞 F) Q * Ideal.relNorm (𝓞 F) J) :=
      FiniteMultiplicity.of_prime_left hvprime (mul_ne_zero (hnormne Q hQ.ne_zero) (hnormne J hJ))
    rw [map_mul, multiplicity_mul hvprime hfinNorm, hprime, IH hJ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    rw [multiplicity_mul (hPprime P)
      (FiniteMultiplicity.of_prime_left (hPprime P) (mul_ne_zero hQ.ne_zero hJ)), mul_add]

end Catalan.Thaine
