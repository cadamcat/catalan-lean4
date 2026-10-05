module

public import Catalan.Thaine.LiteralClassUnitPower
public import Catalan.Thaine.LiteralLambdaIdeal
public import Catalan.Thaine.LiteralNormPowers

/-!
# `Catalan.Thaine.LiteralLambdaPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance lambdaPowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

lemma literal_lambda_norm_unit_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q)) :
    ∃ u : (𝓞 (A3.F p))ˣ, ∃ b : (A3.F p)ˣ,
      upow p (A3.F p) (literalLambdaNorm p x (by omega)) (literalRestrictionRing p Theta) =
        Units.map (algebraMap (𝓞 (A3.F p)) (A3.F p)).toMonoidHom u * b ^ q := by
  obtain ⟨J, hJ⟩ := literal_lambda_norm_principal_power p q Fact.out (by omega) hq2 x y hx hy h
  exact literal_annihilator_unit_power p q hp7 hpq hq2 hdegree Theta hTheta
    (literalLambdaNorm p x (by omega)) J hJ

lemma literal_lambda_plus_unit_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q)) :
    ∃ u : (𝓞 (A3.Bsub p p))ˣ, ∃ b : (A3.Bsub p p)ˣ,
      upow p (A3.Bsub p p) (A1e.lambdaUnit p (A3.Bsub p p) x (by omega))
        ((1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) * Theta) =
      Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom u * b ^ q := by
  obtain ⟨u, b, hu⟩ := literal_lambda_norm_unit_power p q hp7 hpq hq2 hdegree x y hx hy h Theta hTheta
  refine ⟨literalRealUnitMap p u, literalFieldUnitMap p b, ?_⟩
  have hmap := congrArg (literalFieldUnitMap p) hu
  dsimp only [literalLambdaNorm] at hmap
  rw [literal_norm_upow_compat p (by omega), map_mul, map_pow, literal_field_integral_unit] at hmap
  exact hmap

end Catalan.Thaine
