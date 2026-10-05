module

public import Mathlib

/-!
# `Catalan.Density.RootResidueCard`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Kummer

lemma prime_dvd_residue_card_sub_one
    (K : Type*) [Field K] [NumberField K] (q ell : ℕ)
    (hq : q.Prime) (hell : ell.Prime) (hqell : q ≠ ell)
    (P : HeightOneSpectrum (𝓞 K)) (hcard : Nat.card (𝓞 K ⧸ P.asIdeal) = ell)
    (zeta : (𝓞 K)ˣ) (hzeta : IsPrimitiveRoot (zeta : 𝓞 K) q) :
    q ∣ ell - 1 := by
  classical
  let F := 𝓞 K ⧸ P.asIdeal
  let rootCardQuotientField : Field F := Ideal.Quotient.field P.asIdeal
  let rootCardQuotientFinite : Finite F := Nat.finite_of_card_ne_zero (hcard ▸ hell.ne_zero)
  let rootCardQuotientFintype : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = ell := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hellZero : (ell : F) = 0 := by
    simpa only [hcard'] using Nat.cast_card_eq_zero F
  let rootCardCharP : CharP F ell := (CharP.charP_iff_prime_eq_zero hell).mpr hellZero
  have hqF : (q : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F hq hqell.symm
  let red : 𝓞 K →+* F := Ideal.Quotient.mk P.asIdeal
  have hzbarne : red (zeta : 𝓞 K) ≠ 1 := by
    intro hzred
    have hsum : (Finset.range q).sum (fun i => (zeta : 𝓞 K) ^ i) = 0 := by
      have h := geom_sum_mul (zeta : 𝓞 K) q
      rw [hzeta.pow_eq_one, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right
        (sub_ne_zero.mpr (hzeta.ne_one hq.one_lt))
    have h := congrArg red hsum
    have hqzero : (q : F) = 0 := by
      simpa only [map_sum, map_pow, hzred, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
    exact hqF hqzero
  have hzbarpow : (red (zeta : 𝓞 K)) ^ q = 1 := by
    rw [← map_pow, hzeta.pow_eq_one, map_one]
  have hzbar : IsPrimitiveRoot (red (zeta : 𝓞 K)) q :=
    isPrimitiveRoot_of_mem_nthRootsFinset hq
      ((Polynomial.mem_nthRootsFinset hq.pos (1 : F)).mpr hzbarpow) hzbarne
  have hz0 : red (zeta : 𝓞 K) ≠ 0 := (Units.map red.toMonoidHom zeta).ne_zero
  apply hzbar.dvd_of_pow_eq_one (ell - 1)
  simpa only [hcard'] using FiniteField.pow_card_sub_one_eq_one (red (zeta : 𝓞 K)) hz0

end Catalan.Kummer
