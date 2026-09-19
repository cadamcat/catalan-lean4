import Catalan.Thaine.CircularizePowers

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance bottomPowerGalComm
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : CommGroup (G p K) := UnitModule.cyclotomicGalCommGroup p K

lemma bottomUnitAnn_integralUnitPow
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hq : 0 < q)
    (Theta : R p K)
    (hTheta : Runge.reduceFull p K q Theta ∈ UnitModule.bottomUnitAnn p K q hq)
    (u : (𝓞 K)ˣ) (hu : u ∈ Circular.primaryCircularUnits p K q) :
    ∃ v : (𝓞 K)ˣ, UnitModule.integralUnitPow p K u Theta = v ^ q := by
  let W := UnitModule.primaryCircularImage p K q hq
  have huW : UnitModule.unitClass p K q u ∈ W :=
    (UnitModule.mem_stableUnitImage_iff p K q (Circular.primaryCircularUnits p K q)
      (Circular.primaryCircularUnits_stable p K q hq) _).mpr ⟨u, hu, rfl⟩
  have hsub := Module.mem_annihilator.mp hTheta
    (⟨UnitModule.unitClass p K q u, huW⟩ : W)
  have hz : UnitModule.unitClass p K q (UnitModule.integralUnitPow p K u Theta) = 0 := by
    rw [unitClass_integralUnitPow]
    exact congrArg (fun x : W => (x : UnitModule.UnitPowerModule p K q)) hsub
  have hpower : UnitQuotient.powerClass q (UnitModule.integralUnitPow p K u Theta) = 0 := by
    simpa only [UnitModule.unitClass, LinearEquiv.apply_symm_apply, map_zero] using
      congrArg (UnitModule.unitRepresentation p K q).asModuleEquiv hz
  have hquot :
      (QuotientGroup.mk (UnitModule.integralUnitPow p K u Theta) :
        (𝓞 K)ˣ ⧸ UnitQuotient.qPowers (𝓞 K)ˣ q) = 1 :=
    congrArg Additive.toMul hpower
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp hquot
  exact ⟨v, hv.symm⟩

lemma pure_power_of_primary_powers
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcard : ¬ q ∣ Nat.card (G p K)) (a : Kˣ)
    (I : Ideal (MonoidAlgebra (ZMod q) (G p K)))
    (hprimary : ∀ Psi : R p K, Runge.reduceFull p K q Psi ∈ I →
      ∃ c : (𝓞 K)ˣ, c ∈ Circular.primaryCircularUnits p K q ∧ ∃ b : Kˣ,
        upow p K a Psi = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q)
    (Theta : R p K)
    (hTheta : Runge.reduceFull p K q Theta ∈
      I * UnitModule.bottomUnitAnn p K q (Fact.out : q.Prime).pos) :
    ∃ b : Kˣ, upow p K a Theta = b ^ q := by
  have hcard0 : (Nat.card (G p K) : ZMod q) ≠ 0 := by
    intro hz
    exact hcard ((ZMod.natCast_eq_zero_iff (Nat.card (G p K)) q).mp hz)
  have bottomPowerCardNeZero : NeZero (Nat.card (G p K) : ZMod q) := ⟨hcard0⟩
  have hThetaI : Runge.reduceFull p K q Theta ∈ I := (Ideal.mul_le_inf hTheta).1
  have hThetaB : Runge.reduceFull p K q Theta ∈
      UnitModule.bottomUnitAnn p K q (Fact.out : q.Prime).pos := (Ideal.mul_le_inf hTheta).2
  obtain ⟨e, he, hB⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (UnitModule.bottomUnitAnn p K q (Fact.out : q.Prime).pos)
  have heB : e ∈ UnitModule.bottomUnitAnn p K q (Fact.out : q.Prime).pos := by
    rw [hB]
    exact Ideal.mem_span_singleton_self e
  obtain ⟨E, hE⟩ := Runge.reduceFull_surjective p K q e
  have hEmem : Runge.reduceFull p K q E ∈
      UnitModule.bottomUnitAnn p K q (Fact.out : q.Prime).pos := by
    rw [hE]
    exact heB
  obtain ⟨c, hc, b, hfactor⟩ := hprimary Theta hThetaI
  obtain ⟨v, hv⟩ := bottomUnitAnn_integralUnitPow p q K (Fact.out : q.Prime).pos E hEmem c hc
  have habs : e * Runge.reduceFull p K q Theta = Runge.reduceFull p K q Theta := by
    have hThetaSpan := hThetaB
    rw [hB] at hThetaSpan
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hThetaSpan
    calc
      _ = e * (e * t) := by rw [ht]
      _ = (e * e) * t := (mul_assoc e e t).symm
      _ = e * t := by rw [he.eq]
      _ = _ := ht.symm
  have hred : Runge.reduceFull p K q (E * Theta) = Runge.reduceFull p K q Theta := by
    rw [map_mul, hE, habs]
  obtain ⟨U, hU⟩ := (Runge.reduceFull_eq_iff_exists_nsmul p K q (E * Theta) Theta).mp hred
  let j := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hpure : upow p K a (E * Theta) = (j v * upow p K b E) ^ q := by
    rw [upow_mul, hfactor, upow_base_mul, upow_pow, ← UnitModule.map_integralUnitPow, hv]
    change j (v ^ q) * upow p K b E ^ q = _
    rw [map_pow, mul_pow]
  refine ⟨(j v * upow p K b E) / upow p K a U, ?_⟩
  calc
    upow p K a Theta = upow p K a (E * Theta) / upow p K a U ^ q := by
      rw [hU, upow_add, Runge.upow_nsmul, mul_div_cancel_right]
    _ = ((j v * upow p K b E) / upow p K a U) ^ q := by
      rw [hpure, div_pow]

end Catalan.Thaine
