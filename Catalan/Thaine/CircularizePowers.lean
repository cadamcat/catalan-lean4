module

public import Catalan.Thaine.LiteralFullAnnihilator
public import Catalan.CaseOne.UnitFiltration
public import Catalan.Runge.PlusIdeal
public import Catalan.Runge.PowerTransport

/-!
# `Catalan.Thaine.CircularizePowers`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance circularizeGalComm
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : CommGroup (G p K) := UnitModule.cyclotomicGalCommGroup p K

lemma topUnitAnn_integralUnitPow
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    (Theta : R p K) (hTheta : Runge.reduceFull p K q Theta ∈ UnitModule.topUnitAnn p K q)
    (u : (𝓞 K)ˣ) :
    ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧ ∃ v : (𝓞 K)ˣ,
      UnitModule.integralUnitPow p K u Theta = c * v ^ q := by
  let W := UnitModule.circularImage p K q
  have hmem : UnitModule.unitClass p K q (UnitModule.integralUnitPow p K u Theta) ∈ W := by
    rw [← W.ker_mkQ]
    change W.mkQ (UnitModule.unitClass p K q (UnitModule.integralUnitPow p K u Theta)) = 0
    rw [unitClass_integralUnitPow, map_smul]
    exact Module.mem_annihilator.mp hTheta (W.mkQ (UnitModule.unitClass p K q u))
  obtain ⟨c, hc, heq⟩ := (UnitModule.mem_stableUnitImage_iff p K q
    (Circular.circularUnits p K) (Circular.circularUnits_stable p K) _).mp hmem
  have hquot :
      (QuotientGroup.mk (UnitModule.integralUnitPow p K u Theta) :
        (𝓞 K)ˣ ⧸ UnitQuotient.qPowers (𝓞 K)ˣ q) = QuotientGroup.mk c := by
    have h := congrArg (UnitModule.unitRepresentation p K q).asModuleEquiv heq.symm
    exact congrArg Additive.toMul h
  obtain ⟨v, hv⟩ := QuotientGroup.eq_iff_div_mem.mp hquot
  refine ⟨c, hc, v, ?_⟩
  rw [hv]
  exact (mul_div_cancel c (UnitModule.integralUnitPow p K u Theta)).symm

lemma circularize_unit_powers
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcard : ¬ q ∣ Nat.card (G p K)) (a : Kˣ)
    (hunit : ∀ Psi : R p K,
      Runge.reduceFull p K q Psi ∈ UnitModule.topUnitAnn p K q →
      ∃ u : (𝓞 K)ˣ, ∃ b : Kˣ,
        upow p K a Psi = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * b ^ q)
    (Theta : R p K) (hTheta : Runge.reduceFull p K q Theta ∈ UnitModule.topUnitAnn p K q) :
    ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧ ∃ b : Kˣ,
      upow p K a Theta = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q := by
  have hcard0 : (Nat.card (G p K) : ZMod q) ≠ 0 := by
    intro hz
    exact hcard ((ZMod.natCast_eq_zero_iff (Nat.card (G p K)) q).mp hz)
  have circularizeCardNeZero : NeZero (Nat.card (G p K) : ZMod q) := ⟨hcard0⟩
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (UnitModule.topUnitAnn p K q)
  have heI : e ∈ UnitModule.topUnitAnn p K q := by
    rw [hI]
    exact Ideal.mem_span_singleton_self e
  obtain ⟨E, hE⟩ := Runge.reduceFull_surjective p K q e
  have hEmem : Runge.reduceFull p K q E ∈ UnitModule.topUnitAnn p K q := by
    rw [hE]
    exact heI
  obtain ⟨u, b, hu⟩ := hunit E hEmem
  obtain ⟨c, hc, v, hv⟩ := topUnitAnn_integralUnitPow p q K Theta hTheta u
  have habs : Runge.reduceFull p K q Theta * e = Runge.reduceFull p K q Theta := by
    have hThetaSpan := hTheta
    rw [hI] at hThetaSpan
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hThetaSpan
    calc
      _ = (e * t) * e := by rw [ht]
      _ = (e * e) * t := by ring
      _ = e * t := by rw [he.eq]
      _ = _ := ht.symm
  have hred : Runge.reduceFull p K q (Theta * E) = Runge.reduceFull p K q Theta := by
    rw [map_mul, hE, habs]
  obtain ⟨U, hU⟩ := (Runge.reduceFull_eq_iff_exists_nsmul p K q (Theta * E) Theta).mp hred
  let j := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hproduct : upow p K a (Theta * E) = j c * (j v * upow p K b Theta) ^ q := by
    rw [upow_mul, hu, upow_base_mul, upow_pow, ← UnitModule.map_integralUnitPow, hv]
    change j (c * v ^ q) * upow p K b Theta ^ q = _
    rw [map_mul, map_pow, mul_assoc, ← mul_pow]
  refine ⟨c, hc, j v * upow p K b Theta / upow p K a U, ?_⟩
  calc
    upow p K a Theta = upow p K a (Theta * E) / upow p K a U ^ q := by
      rw [hU, upow_add, Runge.upow_nsmul, mul_div_cancel_right]
    _ = j c * (j v * upow p K b Theta / upow p K a U) ^ q := by
      rw [hproduct, div_pow, mul_div_assoc]

end Catalan.Thaine
