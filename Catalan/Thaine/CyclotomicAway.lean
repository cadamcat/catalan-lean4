import Catalan.Density.InertiaBridge

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma cyclotomic_inertia_trivial_away
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (ell : ℕ) [Fact ell.Prime] [IsCyclotomicExtension {ell} F L]
    (P : HeightOneSpectrum (𝓞 L)) (haway : (ell : 𝓞 L) ∉ P.asIdeal) :
    A3.InertiaTrivial F L P.asIdeal := by
  let instNeZeroEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  let z : L := IsCyclotomicExtension.zeta ell F L
  have hz : IsPrimitiveRoot z ell := IsCyclotomicExtension.zeta_spec ell F L
  let zO : 𝓞 L := hz.toInteger
  have hzO : IsPrimitiveRoot zO ell := hz.toInteger_isPrimitiveRoot
  let Q := 𝓞 L ⧸ P.asIdeal
  let red : (𝓞 L) →+* Q := Ideal.Quotient.mk P.asIdeal
  have hellbar : (ell : Q) ≠ 0 := by
    intro hzero
    apply haway
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change red (ell : 𝓞 L) = 0
    simpa only [map_natCast] using hzero
  have hbarne : red zO ≠ 1 := by
    intro hred
    have hsum : (Finset.range ell).sum (fun i => zO ^ i) = 0 := by
      have h := geom_sum_mul zO ell
      rw [hzO.pow_eq_one, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right
        (sub_ne_zero.mpr (hzO.ne_one (Fact.out : ell.Prime).one_lt))
    have h := congrArg red hsum
    have hzero : (ell : Q) = 0 := by
      simpa only [map_sum, map_pow, hred, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
    exact hellbar hzero
  have hbarpow : (red zO) ^ ell = 1 := by
    rw [← map_pow, hzO.pow_eq_one, map_one]
  have hbar : IsPrimitiveRoot (red zO) ell := by
    apply isPrimitiveRoot_of_mem_nthRootsFinset (Fact.out : ell.Prime)
    · exact (Polynomial.mem_nthRootsFinset (Fact.out : ell.Prime).pos (1 : Q)).mpr hbarpow
    · exact hbarne
  intro σ hσP hσdiff
  have hsrootpow : (σ z) ^ ell = 1 := by
    rw [← map_pow, hz.pow_eq_one, map_one]
  obtain ⟨a, ha, hpow⟩ := hz.eq_pow_of_pow_eq_one hsrootpow
  have hIntPow : A3.integralAut σ zO = zO ^ a := by
    apply RingOfIntegers.coe_injective
    change σ (zO : L) = (zO : L) ^ a
    dsimp only [zO]
    calc
      σ (hz.toInteger : L) = σ z := congrArg σ hz.coe_toInteger
      _ = z ^ a := hpow.symm
      _ = (hz.toInteger : L) ^ a := congrArg (fun x : L => x ^ a) hz.coe_toInteger.symm
  have hbarσ : red (A3.integralAut σ zO) = red zO := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    exact hσdiff zO
  rw [hIntPow] at hbarσ
  have haone : a = 1 := hbar.pow_inj ha (Fact.out : ell.Prime).one_lt (by simpa using hbarσ)
  have hrootfix : σ z = z := by
    rw [← hpow, haone, pow_one]
  apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq {ell} F L
  intro n hn hn0
  simp only [Set.mem_singleton_iff] at hn
  subst n
  exact ⟨z, hz, by simpa using hrootfix⟩

lemma cyclotomic_isUnramifiedAt_away
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (ell : ℕ) [Fact ell.Prime] [IsCyclotomicExtension {ell} F L]
    (P : HeightOneSpectrum (𝓞 L)) (haway : (ell : 𝓞 L) ∉ P.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
  let instGalois : IsGalois F L := IsCyclotomicExtension.isGalois {ell} F L
  exact (A3.inertiaTrivial_iff_isUnramifiedAt F L P.asIdeal P.ne_bot).mp
    (cyclotomic_inertia_trivial_away F L ell P haway)

end Catalan.Thaine
