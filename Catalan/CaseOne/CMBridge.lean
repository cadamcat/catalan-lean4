import Catalan.CaseOne.TorsionReduction

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitQuotient

noncomputable def realUnitInclusion (K : Type*) [Field K] [NumberField K] :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
  Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom

noncomputable def realUnitPowerMap (K : Type*) [Field K] [NumberField K] (q : ℕ) :
    PowerQuotient (𝓞 (NumberField.maximalRealSubfield K))ˣ q →ₗ[ZMod q]
      PowerQuotient (𝓞 K)ˣ q :=
  powerMap q (realUnitInclusion K)

lemma realUnitPowerMap_bijective
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp2 : 2 < p) (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Bijective (realUnitPowerMap K q) := by
  classical
  have instCM : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField K (S := {p}) ⟨p, by simp, hp2⟩
  let c : (𝓞 K)ˣ ≃* (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K
  have hc2 (u : (𝓞 K)ˣ) : c (c u) = u := by
    apply Units.ext
    apply RingOfIntegers.ext
    change NumberField.IsCMField.complexConj K
      (NumberField.IsCMField.complexConj K ((u : 𝓞 K) : K)) = ((u : 𝓞 K) : K)
    exact NumberField.IsCMField.complexConj_apply_apply K _
  have hinc : Function.Injective (realUnitInclusion K) :=
    Units.map_injective (RingOfIntegers.algebraMap.injective (NumberField.maximalRealSubfield K) K)
  have hfixed (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
      c (realUnitInclusion K u) = realUnitInclusion K u := by
    apply (NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    exact ⟨u, rfl⟩
  have hpowers : Function.Injective (fun u : (𝓞 K)ˣ => u ^ q) := by
    let e : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
    have he : Function.Injective e := Units.map_injective RingOfIntegers.coe_injective
    intro a b hab
    apply he
    apply unit_pow_injective p K q hpq hq2
    simpa only [map_pow] using congrArg e hab
  constructor
  · apply (injective_iff_map_eq_zero (realUnitPowerMap K q)).mpr
    intro z hz
    induction z using QuotientGroup.induction_on with
    | _ u =>
      change (QuotientGroup.mk (realUnitInclusion K u) : (𝓞 K)ˣ ⧸ qPowers (𝓞 K)ˣ q) = 1 at hz
      obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff (realUnitInclusion K u)).mp hz
      have hvfixed : c v = v := by
        apply hpowers
        change (c v) ^ q = v ^ q
        rw [← map_pow, hv, hfixed]
      have hvreal : v ∈ NumberField.IsCMField.realUnits K :=
        (NumberField.IsCMField.unitsComplexConj_eq_self_iff K v).mp hvfixed
      obtain ⟨w, hw⟩ := hvreal
      change realUnitInclusion K w = v at hw
      change (QuotientGroup.mk u : (𝓞 (NumberField.maximalRealSubfield K))ˣ ⧸
        qPowers (𝓞 (NumberField.maximalRealSubfield K))ˣ q) = 1
      apply (QuotientGroup.eq_one_iff u).mpr
      refine ⟨w, hinc ?_⟩
      rw [map_pow, hw, hv]
  · intro z
    induction z using QuotientGroup.induction_on with
    | _ u =>
      obtain ⟨t, ht⟩ := (Fact.out : q.Prime).odd_of_ne_two hq2
      let w : (𝓞 K)ˣ := u ^ (t + 1)
      have hwsq : w ^ 2 = u ^ (q + 1) := by
        dsimp only [w]
        rw [← pow_mul]
        congr 1
        omega
      have hnfixed : c (w * c w) = w * c w := by
        rw [map_mul, hc2]
        exact mul_comm _ _
      have hnreal : w * c w ∈ NumberField.IsCMField.realUnits K :=
        (NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mp hnfixed
      obtain ⟨v, hv⟩ := hnreal
      change realUnitInclusion K v = w * c w at hv
      let π : (𝓞 K)ˣ →* (𝓞 K)ˣ ⧸ qPowers (𝓞 K)ˣ q := QuotientGroup.mk' _
      have htor : w * (c w)⁻¹ ∈ NumberField.Units.torsion K :=
        (NumberField.IsCMField.unitsMulComplexConjInv K w).property
      have hπtor : π (w * (c w)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (torsion_le_qPowers p K q hpq hq2 htor)
      have hcclass : π (c w) = π w := by
        rw [map_mul, map_inv] at hπtor
        exact (mul_inv_eq_one.mp hπtor).symm
      have huq : π u ^ q = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
      have hnclass : π (w * c w) = π u := by
        rw [map_mul, hcclass, ← pow_two, ← map_pow, hwsq, map_pow, pow_succ, huq, one_mul]
      refine ⟨powerClass q v, ?_⟩
      change π (realUnitInclusion K v) = π u
      rw [hv]
      exact hnclass

end Catalan.UnitQuotient
