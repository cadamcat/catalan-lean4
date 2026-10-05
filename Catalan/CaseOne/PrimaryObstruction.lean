module

public import Catalan.CaseOne.PrimaryPolynomial
public import Catalan.CaseOne.PrimaryCongruence
public import Catalan.CaseOne.PowerBasisDivisibility

/-!
# `Catalan.CaseOne.PrimaryObstruction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open Polynomial NumberField
noncomputable section
namespace Catalan.Primary
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma not_dvd_primaryPolynomial_eval (q : ℕ) (hq : q.Prime) (hqp : q < p) :
    ¬ (q : 𝓞 K) ∣ aeval (ζ_spec p K).toInteger (primaryPolynomial q) := by
  intro hd
  let pb := (ζ_spec p K).integralPowerBasis
  have hdim : pb.dim = p - 1 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime (Fact.out : p.Prime)]
  have hf : (primaryPolynomial q).natDegree < pb.dim := by
    rw [hdim]
    exact (primaryPolynomial_natDegree_lt q hq.pos).trans_le (by omega)
  have hi : q - 1 < pb.dim := by rw [hdim]; omega
  have hcoeff := powerBasis_dvd_aeval_coeff (𝓞 K) pb (primaryPolynomial q) hf
    (q : ℤ) (by
      simpa only [pb, IsPrimitiveRoot.integralPowerBasis_gen, Int.cast_natCast] using hd)
    ⟨q - 1, hi⟩
  change (q : ℤ) ∣ (primaryPolynomial q).coeff (q - 1) at hcoeff
  rw [primaryPolynomial_coeff_pred q hq] at hcoeff
  exact hq.not_dvd_one (by exact_mod_cast hcoeff)

lemma zeta_sum_not_qth_mod_square (q : ℕ) (hq : q.Prime) (hqp : q < p) :
    ¬ ∃ ν : 𝓞 K, (q : 𝓞 K) ^ 2 ∣ 1 + (ζ_spec p K).toInteger ^ q - ν ^ q := by
  rintro ⟨ν, hν⟩
  let z : 𝓞 K := (ζ_spec p K).toInteger
  let b : 𝓞 K := 1 + z
  have hpoly : (q : 𝓞 K) * aeval z (primaryPolynomial q) = b ^ q - 1 - z ^ q := by
    have he := congrArg (aeval z) (primaryPolynomial_identity q hq)
    simpa only [map_mul, map_sub, map_pow, map_add, map_one, aeval_C, aeval_X,
      map_natCast, b] using he
  have hqP : (q : 𝓞 K) ∣ b ^ q - 1 - z ^ q := ⟨_, hpoly.symm⟩
  have hqA : (q : 𝓞 K) ∣ 1 + z ^ q - ν ^ q :=
    dvd_trans (show (q : 𝓞 K) ∣ (q : 𝓞 K) ^ 2 from ⟨q, by ring⟩) hν
  have hbq : (q : 𝓞 K) ∣ b ^ q - ν ^ q := by
    convert dvd_add hqP hqA using 1 <;> ring
  obtain ⟨F, hF⟩ := A1e.cyclotomic_frobenius_lift p K q hq (Ne.symm (Nat.ne_of_lt hqp))
  have hFdiff : (q : 𝓞 K) ∣ F b - F ν := by
    convert dvd_sub hbq (dvd_sub (hF b) (hF ν)) using 1 <;> ring
  have hroot : (q : 𝓞 K) ∣ b - ν := by
    obtain ⟨c, hc⟩ := hFdiff
    refine ⟨F.symm c, ?_⟩
    simpa only [map_sub, map_mul, map_natCast, RingEquiv.symm_apply_apply] using
      congrArg F.symm hc
  have hpow2 := square_dvd_pow_sub_pow (𝓞 K) q hq b ν hroot
  have hprod : (q : 𝓞 K) ^ 2 ∣ (q : 𝓞 K) * aeval z (primaryPolynomial q) := by
    rw [hpoly]
    convert dvd_sub hpow2 hν using 1 <;> ring
  have hq0 : (q : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hred : (q : 𝓞 K) ∣ aeval z (primaryPolynomial q) := by
    rw [pow_two] at hprod
    exact (mul_dvd_mul_iff_left hq0).mp hprod
  exact not_dvd_primaryPolynomial_eval p K q hq hqp hred

end Catalan.Primary
