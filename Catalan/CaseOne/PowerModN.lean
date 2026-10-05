module

public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.CaseOne.PowerModN`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitQuotient
variable (B : Type*) [CommGroup B] (q : ℕ)

noncomputable def modNToPower :
    ModN (Additive B) q →ₗ[ZMod q] PowerQuotient B q :=
  ModN.liftEquiv'.symm
    ⟨(QuotientGroup.mk' (qPowers B q)).toAdditive,
      fun b => powerQuotient_exponent q (powerClass q (Additive.toMul b))⟩

private lemma modNToPower_apply (b : B) :
    modNToPower B q (ModN.mkQ q (Additive.ofMul b)) = powerClass q b := rfl

lemma modNToPower_bijective : Function.Bijective (modNToPower B q) := by
  constructor
  · apply (injective_iff_map_eq_zero (modNToPower B q)).mpr
    intro v hv
    induction v using QuotientAddGroup.induction_on with
    | _ b =>
      change (QuotientGroup.mk (Additive.toMul b) : B ⧸ qPowers B q) = 1 at hv
      obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff (Additive.toMul b)).mp hv
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨Additive.ofMul a, ?_⟩
      change (q : ℤ) • Additive.ofMul a = b
      rw [natCast_zsmul]
      exact congrArg Additive.ofMul ha
  · intro v
    induction v using QuotientGroup.induction_on with
    | _ b =>
      exact ⟨ModN.mkQ q (Additive.ofMul b), modNToPower_apply B q b⟩

noncomputable def powerQuotientModN :
    PowerQuotient B q ≃ₗ[ZMod q] ModN (Additive B) q :=
  (LinearEquiv.ofBijective (modNToPower B q) (modNToPower_bijective B q)).symm

lemma powerQuotientModN_apply (b : B) :
    powerQuotientModN B q (powerClass q b) = ModN.mkQ q (Additive.ofMul b) := by
  apply (LinearEquiv.ofBijective (modNToPower B q) (modNToPower_bijective B q)).injective
  change (LinearEquiv.ofBijective (modNToPower B q) (modNToPower_bijective B q))
    ((LinearEquiv.ofBijective (modNToPower B q) (modNToPower_bijective B q)).symm
      (powerClass q b)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (modNToPower_apply B q b).symm

end Catalan.UnitQuotient
