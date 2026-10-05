module

public import Catalan.Runge.Definitions
public import Catalan.CaseOne.PowerBasisDivisibility
public import Catalan.Cyclotomic.Ramification

/-!
# `Catalan.Runge.CoefficientBasis`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance coefficientBasisGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma dvd_coeff_of_dvd_zeta_sum (q : ℕ) (Theta : R p K)
    (h : (q : 𝓞 K) ∣ ∑ g : G p K, (Theta.coeff g : 𝓞 K) * zetaConjInt p K g) :
    ∀ g : G p K, (q : ℤ) ∣ Theta.coeff g := by
  classical
  have hp : p.Prime := Fact.out
  have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  let e := IsCyclotomicExtension.Rat.galEquivZMod p K
  let a : G p K → ℕ := fun g => (e g : ZMod p).val
  have hpos (g : G p K) : 0 < a g := ZMod.val_pos.mpr (Units.ne_zero (e g))
  have hlt (g : G p K) : a g < p := ZMod.val_lt (e g : ZMod p)
  have hainj : Function.Injective a := by
    intro g t hgt
    apply e.injective
    apply Units.ext
    exact ZMod.val_injective p hgt
  have hinj : Function.Injective (fun g : G p K => a g - 1) := by
    intro g t hgt
    change a g - 1 = a t - 1 at hgt
    apply hainj
    have hg := hpos g
    have ht := hpos t
    omega
  have hbound (g : G p K) : a g - 1 ≤ p - 2 := by
    have hg := hpos g
    have hg' := hlt g
    omega
  let Z : 𝓞 K := (ζ_spec p K).toInteger
  have hZunit : IsUnit Z := (ζ_spec p K).toInteger_isPrimitiveRoot.isUnit hp.ne_zero
  have hZpow (g : G p K) : Z ^ a g = zetaConjInt p K g := by
    apply RingOfIntegers.coe_injective
    change ζ p K ^ a g = g (ζ p K)
    exact (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p K g
      (ζ_spec p K).pow_eq_one).symm
  let Q : Polynomial ℤ := ∑ g : G p K,
    Polynomial.C (Theta.coeff g) * Polynomial.X ^ (a g - 1)
  have hsum : Z * Polynomial.aeval Z Q =
      ∑ g : G p K, (Theta.coeff g : 𝓞 K) * zetaConjInt p K g := by
    dsimp only [Q]
    simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [← hZpow g]
    have he : a g - 1 + 1 = a g := by have hg := hpos g; omega
    change Z * ((Theta.coeff g : 𝓞 K) * Z ^ (a g - 1)) =
      (Theta.coeff g : 𝓞 K) * Z ^ a g
    calc
      _ = (Theta.coeff g : 𝓞 K) * (Z ^ (a g - 1) * Z) := by ring
      _ = _ := by rw [← pow_succ, he]
  have hdiv : (q : 𝓞 K) ∣ Polynomial.aeval Z Q :=
    hZunit.dvd_mul_left.mp (by rwa [hsum])
  let pb := (ζ_spec p K).integralPowerBasis
  have hdim : pb.dim = p - 1 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime hp]
  have hdegree : Q.natDegree < pb.dim := by
    have hle : Q.natDegree ≤ p - 2 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro g hg
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hbound g)
    rw [hdim]
    have hp2 := hp.two_le
    omega
  have hcoeff (g : G p K) : Q.coeff (a g - 1) = Theta.coeff g := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hinj.eq_iff]
    simp
  intro g
  have hi : a g - 1 < pb.dim := by
    rw [hdim]
    have hg := hbound g
    have hp2 := hp.two_le
    omega
  have hc := Catalan.Primary.powerBasis_dvd_aeval_coeff (𝓞 K) pb Q hdegree
    (q : ℤ) (by
      simpa only [pb, IsPrimitiveRoot.integralPowerBasis_gen, Z, Int.cast_natCast] using hdiv)
    ⟨a g - 1, hi⟩
  change (q : ℤ) ∣ Q.coeff (a g - 1) at hc
  rwa [hcoeff] at hc

end Catalan.Runge
