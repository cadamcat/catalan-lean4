module

public import Catalan.Thaine.LiteralMaps
public import Catalan.Thaine.CircularClosure
public import Catalan.CaseOne.PowerImage
public import Catalan.CaseOne.TorsionReduction

/-!
# `Catalan.Thaine.CircularImageComparison`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

private lemma comparison_root_index
    (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w p) :
    ∃ a : (ZMod p)ˣ, w = z ^ (a : ZMod p).val := by
  have instComparisonIndexNeP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨i, hi, hcop, hpow⟩ := hz.isPrimitiveRoot_iff.mp hw
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi] using hpow.symm

private lemma comparison_pow_mul_index
    (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    (z : K) (hz : IsPrimitiveRoot z p) (a b : (ZMod p)ˣ) :
    z ^ ((a * b : (ZMod p)ˣ) : ZMod p).val =
      (z ^ (a : ZMod p).val) ^ (b : ZMod p).val := by
  have instComparisonPowNeP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Units.val_mul, ZMod.val_mul, ← pow_mul]
  exact (pow_eq_pow_mod _ hz.pow_eq_one).symm

private lemma comparison_ratio_unit
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    (z : K) (hz : IsPrimitiveRoot z p) (a b : (ZMod p)ˣ) :
    ∃ u : (𝓞 K)ˣ, u ∈ Circular.circularUnits p K ∧
      ((u : 𝓞 K) : K) = (1 - z ^ (a : ZMod p).val) / (1 - z ^ (b : ZMod p).val) := by
  obtain ⟨c, hc⟩ := comparison_root_index p (ζ p K) z (ζ_spec p K) hz
  obtain ⟨u, hu⟩ := Circular.exists_ratio_unit p K (c * a) (c * b)
  refine ⟨u, Subgroup.subset_closure (Or.inr ⟨c * a, c * b, hu⟩), ?_⟩
  rw [hu, comparison_pow_mul_index p (ζ p K) (ζ_spec p K),
    comparison_pow_mul_index p (ζ p K) (ζ_spec p K), ← hc]

private lemma comparison_root_unit
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    (z : K) (hz : IsPrimitiveRoot z p) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = z ∧ u ∈ NumberField.Units.torsion K := by
  have hp : p.Prime := Fact.out
  have hunit : IsUnit hz.toInteger := hz.toInteger_isPrimitiveRoot.isUnit hp.ne_zero
  let u : (𝓞 K)ˣ := hunit.unit
  have hu : (u : 𝓞 K) = hz.toInteger := hunit.unit_spec
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact hz.coe_toInteger
  · change IsOfFinOrder u
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨p, hp.pos, ?_⟩
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hu, Units.val_one] using hz.toInteger_isPrimitiveRoot.pow_eq_one

private lemma comparison_real_generator_image
    (p : ℕ) (a : (ZMod p)ˣ) (c : (𝓞 (A3.F p))ˣ)
    (hc : algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) =
      normalizedCircularValue p a (A3.primitiveRoot p)) :
    ((literalRealUnitMap p c : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
      normalizedCircularValue p a (auxiliaryRoot p p) := by
  apply (algebraMap (A3.Bsub p p) A3.Omega).injective
  change algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) = _
  rw [hc]
  simp only [normalizedCircularValue, normalizedEpsilon_map, map_one]
  rfl

private lemma comparison_class_mul {A : Type*} [CommGroup A] (q : ℕ) (a b : A) :
    UnitQuotient.powerClass q (a * b) = UnitQuotient.powerClass q a + UnitQuotient.powerClass q b := rfl

private lemma comparison_class_inv {A : Type*} [CommGroup A] (q : ℕ) (a : A) :
    UnitQuotient.powerClass q a⁻¹ = -UnitQuotient.powerClass q a := rfl

private lemma comparison_real_mem_full
    (p : ℕ) [Fact p.Prime] (c : (𝓞 (A3.F p))ˣ) (hc : c ∈ realCircularUnits p) :
    literalRealUnitMap p c ∈ literalFullCircularUnits p := by
  have instComparisonRealCyclotomic : IsCyclotomicExtension {p} ℚ (A3.Bsub p p) :=
    literalFullCyclotomic p
  let z := auxiliaryRoot p p
  have hz : IsPrimitiveRoot z p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (A3.primitiveRoot_spec p (Fact.out : p.Prime).pos)
  obtain ⟨Z, hZ, hZT⟩ := comparison_root_unit p (A3.Bsub p p) z hz
  have hZfull : Z ∈ literalFullCircularUnits p :=
    Subgroup.subset_closure (Or.inl hZT)
  have hle : realCircularUnits p ≤ (literalFullCircularUnits p).comap (literalRealUnitMap p) := by
    apply (Subgroup.closure_le _).2
    intro d hd
    rcases hd with rfl | ⟨a, ha⟩
    · change literalRealUnitMap p (-1) ∈ literalFullCircularUnits p
      have hneg : literalRealUnitMap p (-1) = -1 := by
        apply Units.ext
        simp [literalRealUnitMap]
      rw [hneg]
      apply Subgroup.subset_closure
      left
      change IsOfFinOrder (-1 : (𝓞 (A3.Bsub p p))ˣ)
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, by simp⟩
    · obtain ⟨r, hr, hrval⟩ := comparison_ratio_unit p (A3.Bsub p p) z hz a 1
      have hprod : literalRealUnitMap p d = Z ^ normalizedHalf p a * r := by
        apply Units.ext
        apply RingOfIntegers.ext
        change ((literalRealUnitMap p d : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
          ((Z : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) ^ normalizedHalf p a *
            ((r : 𝓞 (A3.Bsub p p)) : A3.Bsub p p)
        rw [comparison_real_generator_image p a d ha, hZ, hrval, normalizedCircularValue_eq]
        simp only [Units.val_one, ZMod.val_one, pow_one]
        rw [mul_div_assoc]
      change literalRealUnitMap p d ∈ literalFullCircularUnits p
      rw [hprod]
      exact (literalFullCircularUnits p).mul_mem ((literalFullCircularUnits p).pow_mem hZfull _) hr
  exact hle hc

lemma full_real_circular_powerImage
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Submodule.map (literalRealPowerMap p q)
      (UnitQuotient.powerImage ((𝓞 (A3.F p))ˣ) q (realCircularUnits p)) =
      UnitQuotient.powerImage ((𝓞 (A3.Bsub p p))ˣ) q (literalFullCircularUnits p) := by
  have instComparisonCyclotomic : IsCyclotomicExtension {p} ℚ (A3.Bsub p p) :=
    literalFullCyclotomic p
  have hp : p.Prime := Fact.out
  let T := Submodule.map (literalRealPowerMap p q)
    (UnitQuotient.powerImage ((𝓞 (A3.F p))ˣ) q (realCircularUnits p))
  change T = _
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨d, hd, rfl⟩ := (UnitQuotient.mem_powerImage_iff _ _ _ _).mp hx
    apply (UnitQuotient.mem_powerImage_iff _ _ _ _).mpr
    exact ⟨literalRealUnitMap p d, comparison_real_mem_full p d hd, rfl⟩
  · let S : Subgroup (𝓞 (A3.Bsub p p))ˣ :=
      { carrier := {u | UnitQuotient.powerClass q u ∈ T}
        one_mem' := by
          change (0 : UnitQuotient.PowerQuotient (𝓞 (A3.Bsub p p))ˣ q) ∈ T
          exact T.zero_mem
        mul_mem' := by
          intro a b ha hb
          change UnitQuotient.powerClass q (a * b) ∈ T
          rw [comparison_class_mul]
          exact T.add_mem ha hb
        inv_mem' := by
          intro a ha
          change UnitQuotient.powerClass q a⁻¹ ∈ T
          rw [comparison_class_inv]
          exact T.neg_mem ha }
    have htor (u : (𝓞 (A3.Bsub p p))ˣ) (hu : u ∈ NumberField.Units.torsion (A3.Bsub p p)) :
        UnitQuotient.powerClass q u = 0 := by
      change (QuotientGroup.mk u : (𝓞 (A3.Bsub p p))ˣ ⧸
        UnitQuotient.qPowers (𝓞 (A3.Bsub p p))ˣ q) = 1
      exact (QuotientGroup.eq_one_iff u).mpr
        (UnitQuotient.torsion_le_qPowers p (A3.Bsub p p) q hpq hq2 hu)
    let z := auxiliaryRoot p p
    have hz : IsPrimitiveRoot z p :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (A3.primitiveRoot_spec p hp.pos)
    let valB : (𝓞 (A3.Bsub p p))ˣ →* A3.Bsub p p :=
      (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom.comp
        (Units.coeHom (𝓞 (A3.Bsub p p)))
    have hvalinj : Function.Injective valB := by
      intro a b h
      apply Units.ext
      apply RingOfIntegers.ext
      exact h
    obtain ⟨Z, hZ, hZT⟩ := comparison_root_unit p (A3.Bsub p p) z hz
    change valB Z = z at hZ
    obtain ⟨j, hj⟩ := comparison_root_index p z (ζ p (A3.Bsub p p)) hz (ζ_spec p (A3.Bsub p p))
    have hfull : literalFullCircularUnits p ≤ S := by
      apply (Subgroup.closure_le S).2
      intro u hu
      rcases hu with huT | ⟨a, b, huval⟩
      · change UnitQuotient.powerClass q u ∈ T
        rw [htor u huT]
        exact T.zero_mem
      · let a' := j * a
        let b' := j * b
        have hza : ζ p (A3.Bsub p p) ^ (a : ZMod p).val = z ^ (a' : ZMod p).val := by
          rw [hj]
          exact (comparison_pow_mul_index p z hz j a).symm
        have hzb : ζ p (A3.Bsub p p) ^ (b : ZMod p).val = z ^ (b' : ZMod p).val := by
          rw [hj]
          exact (comparison_pow_mul_index p z hz j b).symm
        obtain ⟨ca, hca, hcaOmega⟩ := exists_real_circular_generator p hp2 a'
        obtain ⟨cb, hcb, hcbOmega⟩ := exists_real_circular_generator p hp2 b'
        have hcaB : valB (literalRealUnitMap p ca) = normalizedCircularValue p a' z :=
          comparison_real_generator_image p a' ca hcaOmega
        have hcbB : valB (literalRealUnitMap p cb) = normalizedCircularValue p b' z :=
          comparison_real_generator_image p b' cb hcbOmega
        have hd : ca / cb ∈ realCircularUnits p := (realCircularUnits p).div_mem hca hcb
        let tor : (𝓞 (A3.Bsub p p))ˣ := Z ^ normalizedHalf p b' / Z ^ normalizedHalf p a'
        have htorT : tor ∈ NumberField.Units.torsion (A3.Bsub p p) :=
          (NumberField.Units.torsion (A3.Bsub p p)).div_mem
            ((NumberField.Units.torsion (A3.Bsub p p)).pow_mem hZT _)
            ((NumberField.Units.torsion (A3.Bsub p p)).pow_mem hZT _)
        have htorval : valB tor = z ^ normalizedHalf p b' / z ^ normalizedHalf p a' := by
          simp only [tor, map_div, map_pow, hZ]
        have huB : valB u = (1 - z ^ (a' : ZMod p).val) / (1 - z ^ (b' : ZMod p).val) := by
          change ((u : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) = _
          rw [huval, hza, hzb]
        have huEq : u = tor * literalRealUnitMap p (ca / cb) := by
          apply hvalinj
          simp only [map_mul, map_div, htorval, hcaB, hcbB, huB, normalizedCircularValue_eq]
          have hz0 : z ≠ 0 := hz.ne_zero hp.ne_zero
          have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (hz.ne_one hp.one_lt).symm
          have hdenb : 1 - z ^ (b' : ZMod p).val ≠ 0 := sub_ne_zero.mpr
            ((hz.pow_of_coprime _ (ZMod.val_coe_unit_coprime b')).ne_one hp.one_lt).symm
          field_simp [hz0, hden, hdenb]
        have hiT : UnitQuotient.powerClass q (literalRealUnitMap p (ca / cb)) ∈ T := by
          refine ⟨UnitQuotient.powerClass q (ca / cb), ?_, rfl⟩
          exact (UnitQuotient.mem_powerImage_iff _ _ _ _).mpr ⟨ca / cb, hd, rfl⟩
        change UnitQuotient.powerClass q u ∈ T
        rw [huEq, comparison_class_mul, htor tor htorT, zero_add]
        exact hiT
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (UnitQuotient.mem_powerImage_iff _ _ _ _).mp hy
    exact hfull hu

end Catalan.Thaine
