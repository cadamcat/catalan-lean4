module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.CharP.Defs

/-!
# Arithmetic of quotients of the ring of integers

Three small API lemmas used by the Stickelberger tower argument:

* `charP_quotient_pow_of_mem`: the characteristic of `A ⧸ I ^ k` is `ell` as soon as
  `ell` is a prime lying in `I ^ k` and `I ^ k` is proper;
* `absNorm_coprime_of_not_dvd`: the absolute norm of a maximal ideal of residue
  characteristic `ell` is coprime to any `n` not divisible by `ell`;
* `isPrimitiveRoot_quotient_of_not_dvd`: a primitive `n`-th root of unity in `𝓞 K` stays
  primitive modulo such a maximal ideal.
-/

/-!
# `Catalan.Stickelberger.TowerArith`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Stickelberger

/-- Auxiliary: the quotient by a proper ideal containing a prime `ell` has characteristic
`ell`. -/
theorem charP_quotient_of_mem {A : Type*} [CommRing A] (J : Ideal A) (ell : ℕ)
    (hell : ell.Prime) (hJ : J ≠ ⊤) (hmem : (ell : A) ∈ J) :
    CharP (A ⧸ J) ell := by
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  refine (CharP.charP_iff_prime_eq_zero hell).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

/-- 商环 A ⧸ I^k 的特征：ell 落在 I^k 里且 I^k ≠ ⊤ 就足够。 -/
theorem charP_quotient_pow_of_mem {A : Type*} [CommRing A] (I : Ideal A) (ell : ℕ)
    (hell : ell.Prime) (k : ℕ) (hk : I ^ k ≠ ⊤) (hmem : (ell : A) ∈ I ^ k) :
    CharP (A ⧸ I ^ k) ell :=
  charP_quotient_of_mem (I ^ k) ell hell hk hmem

/-- 极大理想的绝对范数与不被其剩余特征整除的 n 互素。 -/
theorem absNorm_coprime_of_not_dvd {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) [I.IsMaximal]
    (ell n : ℕ) (hell : ell.Prime)
    (hmem : (ell : NumberField.RingOfIntegers K) ∈ I) (hdvd : ¬ ell ∣ n) :
    (Ideal.absNorm I).Coprime n := by
  obtain ⟨p, m, -, hpI, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow I
  have hne : I ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have h1 : CharP (NumberField.RingOfIntegers K ⧸ I) ell :=
    charP_quotient_of_mem I ell hell hne hmem
  have h2 : CharP (NumberField.RingOfIntegers K ⧸ I) p :=
    charP_quotient_of_mem I p hp hne hpI
  have hpe : p = ell := CharP.eq _ h2 h1
  rw [hnorm, hpe]
  exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hell).mpr hdvd)

/-- 在整数环里，模去与 n 互素范数的极大理想保持 n 次本原单位根。 -/
theorem isPrimitiveRoot_quotient_of_not_dvd {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) [I.IsMaximal]
    (n ell : ℕ) [NeZero n] (hell : ell.Prime)
    (hmem : (ell : NumberField.RingOfIntegers K) ∈ I) (hdvd : ¬ ell ∣ n)
    {μ : NumberField.RingOfIntegers K} (hμ : IsPrimitiveRoot μ n) :
    IsPrimitiveRoot (Ideal.Quotient.mk I μ) n :=
  hμ.idealQuotient_mk
    (Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsMaximal.ne_top inferInstance))
    (absNorm_coprime_of_not_dvd I ell n hell hmem hdvd)

end Catalan.Stickelberger
