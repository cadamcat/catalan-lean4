import Catalan.Thaine.LiteralMaps
import Catalan.Thaine.IntegralUnitDescent
import Catalan.Cyclotomic.UnitPowers
import Catalan.Density.NormalM

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma literal_real_unit_powerMap_injective
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Injective (literalRealPowerMap p q) := by
  have literalPowerInjectionFullCyclotomic :
      IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p
  have literalPowerInjectionRelativeGalois : IsGalois (A3.F p) (A3.Bsub p p) :=
    A3.isGalois_Bsub p p (Fact.out : p.Prime).pos
  have hmapinj : Function.Injective (literalRealUnitMap p) := by
    intro u v huv
    apply Units.ext
    apply RingOfIntegers.ext
    apply (algebraMap (A3.F p) (A3.Bsub p p)).injective
    exact congrArg (fun w : (𝓞 (A3.Bsub p p))ˣ => ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p)) huv
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  induction c using QuotientGroup.induction_on with
  | _ u =>
    change literalRealPowerMap p q (UnitQuotient.powerClass q u) = 0 at hc
    rw [literalRealPowerMap, UnitQuotient.powerMap_apply] at hc
    have hu : literalRealUnitMap p u ∈ UnitQuotient.qPowers (𝓞 (A3.Bsub p p))ˣ q := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Additive.toMul hc
    obtain ⟨w, hw⟩ := hu
    have hwField : ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) ^ q =
        algebraMap (A3.F p) (A3.Bsub p p) ((u : 𝓞 (A3.F p)) : A3.F p) := by
      have h := congrArg
        (fun y : (𝓞 (A3.Bsub p p))ˣ => ((y : 𝓞 (A3.Bsub p p)) : A3.Bsub p p)) hw
      change ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) ^ q =
        algebraMap (A3.F p) (A3.Bsub p p) ((u : 𝓞 (A3.F p)) : A3.F p) at h
      exact h
    let wField : (A3.Bsub p p)ˣ :=
      Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom w
    have hfixed : ∀ tau : A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p,
        tau ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
          ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) := by
      intro tau
      have hpow : (Units.map tau.toRingEquiv.toRingHom.toMonoidHom wField) ^ q = wField ^ q := by
        apply Units.ext
        change tau ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) ^ q =
          ((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) ^ q
        rw [← map_pow, hwField, tau.commutes]
      have hunit := unit_pow_injective p (A3.Bsub p p) q hpq hq2 hpow
      exact congrArg (fun y : (A3.Bsub p p)ˣ => (y : A3.Bsub p p)) hunit
    obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := A3.F p)
      (((w : 𝓞 (A3.Bsub p p)) : A3.Bsub p p))).mpr hfixed
    obtain ⟨v, _, hv⟩ := exists_integral_unit_of_field_image
      (A3.F p) (A3.Bsub p p) w x hx
    have hvmap : literalRealUnitMap p v = w := hv
    have hvpow : v ^ q = u := hmapinj (by rw [map_pow, hvmap]; exact hw)
    change (QuotientGroup.mk u : (𝓞 (A3.F p))ˣ ⧸ UnitQuotient.qPowers (𝓞 (A3.F p))ˣ q) = 1
    exact (QuotientGroup.eq_one_iff u).mpr ⟨v, hvpow⟩

end Catalan.Thaine
