module

public import Catalan.Thaine.CircularizePowers
public import Catalan.Thaine.LiteralLambdaPower

/-!
# `Catalan.Thaine.LiteralCircularPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance literalCircularPowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance literalCircularPowerGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_lambda_plus_circular_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈ UnitModule.topUnitAnn p (A3.Bsub p p) q) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.circularUnits p (A3.Bsub p p) ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (A1e.lambdaUnit p (A3.Bsub p p) x (by omega))
          ((1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) * Theta) =
        Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  let P : R p (A3.Bsub p p) := 1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1
  let lam := A1e.lambdaUnit p (A3.Bsub p p) x (by omega)
  have hunit (Psi : R p (A3.Bsub p p))
      (hPsi : Runge.reduceFull p (A3.Bsub p p) q Psi ∈ UnitModule.topUnitAnn p (A3.Bsub p p) q) :
      ∃ u : (𝓞 (A3.Bsub p p))ˣ, ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (upow p (A3.Bsub p p) lam P) Psi =
          Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom u * b ^ q := by
    rw [← upow_mul, mul_comm Psi P]
    exact literal_lambda_plus_unit_power p q hp7 hpq hq2 hdegree x y hx hy h Psi hPsi
  have hc := circularize_unit_powers p q (A3.Bsub p p)
    (literal_full_gal_card_not_dvd p q (by omega) hq2 hdegree)
    (upow p (A3.Bsub p p) lam P) hunit Theta hTheta
  rw [← upow_mul, mul_comm Theta P] at hc
  exact hc

end Catalan.Thaine
