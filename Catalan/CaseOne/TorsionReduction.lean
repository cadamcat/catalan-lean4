module

public import Catalan.CaseOne.PowerQuotient
public import Catalan.Cyclotomic.UnitPowers

/-!
# `Catalan.CaseOne.TorsionReduction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitQuotient

noncomputable def unitTorsionMap (K : Type*) [Field K] [NumberField K] (q : ℕ) :
    PowerQuotient (𝓞 K)ˣ q →ₗ[ZMod q]
      PowerQuotient ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) q :=
  powerMap q (QuotientGroup.mk' (NumberField.Units.torsion K))

lemma torsion_le_qPowers
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    NumberField.Units.torsion K ≤ qPowers (𝓞 K)ˣ q := by
  let e : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have he : Function.Injective e := Units.map_injective RingOfIntegers.coe_injective
  have hinj : Function.Injective (fun u : (𝓞 K)ˣ => u ^ q) := by
    intro a b hab
    apply he
    apply unit_pow_injective p K q hpq hq2
    simpa only [map_pow] using congrArg e hab
  have hinjT : Function.Injective (fun u : NumberField.Units.torsion K => u ^ q) := by
    intro a b hab
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hab)
  have hsurj := Finite.surjective_of_injective hinjT
  intro u hu
  obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
  exact ⟨(v : (𝓞 K)ˣ), congrArg Subtype.val hv⟩

lemma unitTorsionMap_bijective_of_torsion_le
    (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (hT : NumberField.Units.torsion K ≤ qPowers (𝓞 K)ˣ q) :
    Function.Bijective (unitTorsionMap K q) := by
  let instTorsionQuotComm : IsMulCommutative ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    ⟨⟨fun a b => Quotient.inductionOn₂' a b fun a b =>
      congrArg (QuotientGroup.mk' (NumberField.Units.torsion K)) (mul_comm a b)⟩⟩
  constructor
  · apply (injective_iff_map_eq_zero (unitTorsionMap K q)).mpr
    intro v hv
    induction v using QuotientGroup.induction_on with
    | _ b =>
      change (QuotientGroup.mk (QuotientGroup.mk b) :
        ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) ⧸
          qPowers ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) q) = 1 at hv
      obtain ⟨d, hd⟩ := (QuotientGroup.eq_one_iff
        (N := qPowers ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) q)
        (QuotientGroup.mk' (NumberField.Units.torsion K) b)).mp hv
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion K) d
      have hmem : b / a ^ q ∈ NumberField.Units.torsion K := by
        apply (QuotientGroup.eq_one_iff (b / a ^ q)).mp
        change (QuotientGroup.mk' (NumberField.Units.torsion K)) (b / a ^ q) = 1
        rw [map_div, map_pow, hd]
        exact div_self' _
      obtain ⟨c, hc⟩ := hT hmem
      change (QuotientGroup.mk b : (𝓞 K)ˣ ⧸ qPowers (𝓞 K)ˣ q) = 1
      apply (QuotientGroup.eq_one_iff b).mpr
      exact ⟨c * a, by rw [mul_pow, hc, div_mul_cancel]⟩
  · intro v
    induction v using QuotientGroup.induction_on with
    | _ d =>
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion K) d
      exact ⟨powerClass q b, rfl⟩

lemma unitTorsionMap_bijective
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Bijective (unitTorsionMap K q) := by
  exact unitTorsionMap_bijective_of_torsion_le K q (torsion_le_qPowers p K q hpq hq2)

end Catalan.UnitQuotient
