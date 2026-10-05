module

public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.CaseOne.PowerImage`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitQuotient
variable (B : Type*) [CommGroup B] (q : ℕ)

noncomputable def powerImage (C : Subgroup B) : Submodule (ZMod q) (PowerQuotient B q) :=
  LinearMap.range (powerMap q C.subtype)

lemma mem_powerImage_iff (C : Subgroup B) (v : PowerQuotient B q) :
    v ∈ powerImage B q C ↔ ∃ c : B, c ∈ C ∧ powerClass q c = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := (LinearMap.mem_range.mp hv)
    induction w using QuotientGroup.induction_on with
    | _ c =>
      refine ⟨(c : B), c.property, ?_⟩
      exact (powerMap_apply q C.subtype c).symm.trans hw
  · rintro ⟨c, hc, rfl⟩
    change powerClass q c ∈ LinearMap.range (powerMap q C.subtype)
    refine ⟨powerClass q ⟨c, hc⟩, ?_⟩
    rw [powerMap_apply]
    rfl

lemma powerImage_inf_eq_iff (C H : Subgroup B) (hpow : qPowers B q ≤ H) :
    powerImage B q (C ⊓ H) = powerImage B q C ↔ C ≤ H := by
  constructor
  · intro himage c hc
    have hcimage : powerClass q c ∈ powerImage B q C :=
      (mem_powerImage_iff B q C (powerClass q c)).mpr ⟨c, hc, rfl⟩
    rw [← himage] at hcimage
    obtain ⟨d, hd, hclass⟩ :=
      (mem_powerImage_iff B q (C ⊓ H) (powerClass q c)).mp hcimage
    have hquot : QuotientGroup.mk d = QuotientGroup.mk c :=
      congrArg Additive.toMul hclass
    have hrel : QuotientGroup.mk (c * d⁻¹) = (1 : B ⧸ qPowers B q) := by
      calc
        QuotientGroup.mk (c * d⁻¹) = QuotientGroup.mk c * (QuotientGroup.mk d)⁻¹ := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        _ = QuotientGroup.mk d * (QuotientGroup.mk d)⁻¹ := by rw [hquot]
        _ = 1 := by simp
    have hrel' : c * d⁻¹ ∈ qPowers B q :=
      (QuotientGroup.eq_one_iff (c * d⁻¹)).mp hrel
    have hcH : c * d⁻¹ ∈ H := hpow hrel'
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).2
    simpa [inv_mul_cancel] using H.mul_mem hcH hdH
  · intro hCH
    rw [inf_eq_left.mpr hCH]

end Catalan.UnitQuotient
