import Catalan.Thaine.PrimaryGoodLift
import Catalan.Thaine.GroupRingStructure
import Catalan.Thaine.LiteralIntegerClassAction
import Catalan.Thaine.LiteralFullThaine
import Catalan.CaseOne.GaloisRing
import Catalan.Runge.PowerTransport
import Mathlib.NumberTheory.NumberField.ClassNumber

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine
attribute [local instance] primaryGroupRingFinite primaryGroupRingCharP

local instance primaryLiftCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance primaryLiftGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_full_gal_card_not_dvd
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hdegree : ¬ q ∣ (p - 1) / 2) : ¬ q ∣ Nat.card (G p (A3.Bsub p p)) := by
  have hcard : Nat.card (G p (A3.Bsub p p)) = 2 * ((p - 1) / 2) := by
    rw [UnitModule.cyclotomicGal_card]
    obtain ⟨r, hr⟩ := (Fact.out : p.Prime).even_sub_one hp2
    omega
  rw [hcard]
  intro hd
  rcases (Fact.out : q.Prime).dvd_mul.mp hd with htwo | hhalf
  · rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h1 | h2
    · exact (Fact.out : q.Prime).ne_one h1
    · exact hq2 h2
  · exact hdegree hhalf

lemma literal_full_annihilator_good_primary_lift
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q)) :
    ∃ n : ℕ, 0 < n ∧
      Runge.reduceFull p (A3.Bsub p p) q (Theta ^ n) = Runge.reduceFull p (A3.Bsub p p) q Theta ∧
      ∀ a : Additive (ClassGroup (𝓞 (A3.F p))),
        (∃ k : ℕ, (q ^ k) • a = 0) → literalIntegerClassAction p (Theta ^ n) a = 0 := by
  have instReduced : IsReduced (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p))) :=
    groupRing_isReduced _ q (literal_full_gal_card_not_dvd p q (by omega) hq2 hdegree)
  apply exists_good_primary_power (R p (A3.Bsub p p))
    (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p))) q (Runge.reduceFull p (A3.Bsub p p) q)
    (Additive (ClassGroup (𝓞 (A3.F p)))) (literalIntegerClassAction p) Theta
  exact literalIntegerClassAction_image_nsmul p q Theta
    (literal_full_circular_annihilator_kills_class_quotient p q hp7 hpq hq2 hdegree Theta hTheta)

lemma literal_full_annihilator_kills_q_torsion
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q))
    (a : Additive (ClassGroup (𝓞 (A3.F p)))) (ha : q • a = 0) :
    literalIntegerClassAction p Theta a = 0 := by
  obtain ⟨n, _, hred, hn⟩ := literal_full_annihilator_good_primary_lift p q hp7 hpq hq2 hdegree Theta hTheta
  obtain ⟨U, hU⟩ := (Runge.reduceFull_eq_iff_exists_nsmul p (A3.Bsub p p) q (Theta ^ n) Theta).mp hred
  have hz := hn a ⟨1, by simpa only [pow_one] using ha⟩
  rw [hU, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply] at hz
  have hzero : q • literalIntegerClassAction p U a = 0 := by
    rw [← map_nsmul, ha, map_zero]
  simpa only [hzero, add_zero] using hz

end Catalan.Thaine
