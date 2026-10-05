module

public import Catalan.Thaine.LiteralCircularPower
public import Catalan.Thaine.RawPiCircularPower
public import Catalan.Thaine.PlusAugmentationLift
public import Catalan.Thaine.CircularPowerTransport
public import Catalan.Cyclotomic.GroupRingMul

/-!
# `Catalan.Thaine.LiteralRootCircularPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance rootCircularPowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance rootCircularPowerGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_xm_zeta_plus_circular_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈ UnitModule.topUnitAnn p (A3.Bsub p p) q)
    (hw : (q : ℤ) ∣ weight p (A3.Bsub p p) Theta) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.circularUnits p (A3.Bsub p p) ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega))
          ((1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) * Theta) =
        Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  let P : R p (A3.Bsub p p) := 1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1
  let pi : (A3.Bsub p p)ˣ := Units.mk0 (1 - ζ p (A3.Bsub p p))
    (sub_ne_zero.mpr ((ζ_spec p (A3.Bsub p p)).ne_one (Fact.out : p.Prime).one_lt).symm)
  have hpi : (pi : A3.Bsub p p) = 1 - ζ p (A3.Bsub p p) := rfl
  have hweight : (q : ℤ) ∣ weight p (A3.Bsub p p) (P * Theta) := by
    rw [weight_mul]
    exact dvd_mul_of_dvd_right hw _
  obtain ⟨c, hc, b, hb⟩ := literal_lambda_plus_circular_power p q hp7 hpq hq2 hdegree
    x y hx hy h Theta hTheta
  obtain ⟨d, hd, v, hv⟩ := raw_pi_circular_power p q (A3.Bsub p p) pi hpi (P * Theta) hweight
  have hfactor : A1e.lambdaUnit p (A3.Bsub p p) x (by omega) * pi =
      xmζ p (A3.Bsub p p) x (by omega) := by
    change (xmζ p (A3.Bsub p p) x (by omega) / pi) * pi = _
    exact div_mul_cancel _ _
  refine ⟨c * d, (Circular.circularUnits p (A3.Bsub p p)).mul_mem hc hd, b * v, ?_⟩
  change upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) (P * Theta) = _
  rw [← hfactor, upow_base_mul, hb, hv, map_mul, mul_pow]
  let φ := Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom
  calc
    (φ c * b ^ q) * (φ d * v ^ q) =
      (φ c * φ d) * (b ^ q * v ^ q) := by
      calc
        (φ c * b ^ q) * (φ d * v ^ q) =
            φ c * (b ^ q * (φ d * v ^ q)) := by rw [mul_assoc]
        _ = φ c * (φ d * (b ^ q * v ^ q)) := by
          congr 1
          rw [← mul_assoc, mul_comm (b ^ q) (φ d), mul_assoc]
        _ = (φ c * φ d) * (b ^ q * v ^ q) := by rw [← mul_assoc]

lemma literal_xm_zeta_circular_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.circularUnits p (A3.Bsub p p) ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) Theta =
        Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  obtain ⟨E, hEI, hw, hred⟩ := exists_plus_topAnn_lift p q (A3.Bsub p p) Theta hTheta
  exact circular_power_of_reduceFull_eq p q (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega))
    Theta ((1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) * E) hred.symm
    (literal_xm_zeta_plus_circular_power p q hp7 hpq hq2 hdegree x y hx hy h E hEI hw)

lemma literal_xm_zeta_circular_power_of_solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp7 : 7 ≤ p) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.circularUnits p (A3.Bsub p p) ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) Theta =
        Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  have hpq := A1e.solution_primes_ne p q Fact.out Fact.out (by omega) hq2 x y hx hy h
  have hcard := UnitModule.not_dvd_gal_card_of_solution p (A3.Bsub p p) q (by omega) hq2 x y hx hy h
  rw [UnitModule.cyclotomicGal_card] at hcard
  have hdegree : ¬ q ∣ (p - 1) / 2 := by
    intro hd
    apply hcard
    have hp : p.Prime := Fact.out
    have heven : p - 1 = 2 * ((p - 1) / 2) := by
      obtain ⟨r, hr⟩ := hp.even_sub_one (by omega)
      omega
    rw [heven]
    exact dvd_mul_of_dvd_right hd 2
  exact literal_xm_zeta_circular_power p q hp7 hpq hq2 hdegree x y hx hy h Theta hTheta

end Catalan.Thaine
