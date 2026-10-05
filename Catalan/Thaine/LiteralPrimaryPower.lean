module

public import Catalan.Thaine.PrimaryUpow
public import Catalan.Thaine.LiteralRootCircularPower
public import Catalan.Thaine.SymmetrizedCongruence

/-!
# `Catalan.Thaine.LiteralPrimaryPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance literalPrimaryPowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance literalPrimaryPowerGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_xm_zeta_primary_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.primaryCircularUnits p (A3.Bsub p p) q ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) Theta =
          Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  obtain ⟨E, hEI, hw, hred⟩ := exists_plus_topAnn_lift p q (A3.Bsub p p) Theta hTheta
  obtain ⟨c, hc, b, hfactor⟩ := literal_xm_zeta_plus_circular_power p q hp7 hpq hq2 hdegree
    x y hx hy h E hEI hw
  let P : R p (A3.Bsub p p) := 1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1
  let a : (A3.Bsub p p)ˣ := upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) P
  have hs : (symmetrizedRootFactor p (A3.Bsub p p) x : A3.Bsub p p) = (a : A3.Bsub p p) :=
    symmetrizedRootFactor_coe p (A3.Bsub p p) x (by omega)
  have hsmod (g : G p (A3.Bsub p p)) :
      (q : 𝓞 (A3.Bsub p p)) ^ 2 ∣ integerAut (A3.Bsub p p) g
        (symmetrizedRootFactor p (A3.Bsub p p) x) - 1 :=
    symmetrizedRootFactor_congruent_one_of_solution p q Fact.out (A3.Bsub p p)
      (by omega) hq2 x y hx hy h g
  have hlocal : upow p (A3.Bsub p p) a E =
      Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
    dsimp only [a]
    rw [← upow_mul, mul_comm E P]
    exact hfactor
  have hcprimary : c ∈ UnitQuotient.primaryUnits (𝓞 (A3.Bsub p p)) q :=
    primary_of_upow_eq_unit_mul_pow p q (Fact.out : q.Prime).pos (A3.Bsub p p)
      a (symmetrizedRootFactor p (A3.Bsub p p) x) hs hsmod E c b hlocal
  obtain ⟨U, hU⟩ := (Runge.reduceFull_eq_iff_exists_nsmul p (A3.Bsub p p) q Theta (P * E)).mp hred.symm
  refine ⟨c, ⟨hc, hcprimary⟩, b * upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) U, ?_⟩
  rw [hU, upow_add, Runge.upow_nsmul, hfactor, mul_pow, mul_assoc]

lemma literal_xm_zeta_primary_power_of_solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp7 : 7 ≤ p) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) :
    ∃ c : (𝓞 (A3.Bsub p p))ˣ, c ∈ Circular.primaryCircularUnits p (A3.Bsub p p) q ∧
      ∃ b : (A3.Bsub p p)ˣ,
        upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) Theta =
          Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom c * b ^ q := by
  have hpq := A1e.solution_primes_ne p q Fact.out Fact.out (by omega) hq2 x y hx hy h
  have hcard := UnitModule.not_dvd_gal_card_of_solution p (A3.Bsub p p) q (by omega) hq2 x y hx hy h
  rw [UnitModule.cyclotomicGal_card] at hcard
  have hdegree : ¬ q ∣ (p - 1) / 2 := by
    intro hd
    apply hcard
    have heven : p - 1 = 2 * ((p - 1) / 2) := by
      obtain ⟨r, hr⟩ := (Fact.out : p.Prime).even_sub_one (by omega)
      omega
    rw [heven]
    exact dvd_mul_of_dvd_right hd 2
  exact literal_xm_zeta_primary_power p q hp7 hpq hq2 hdegree x y hx hy h Theta hTheta

end Catalan.Thaine
