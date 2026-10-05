module

public import Catalan.Density.DualLeft
public import Catalan.Density.DualRight

/-!
# `Catalan.Density.PerfectKummer`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NumberField
noncomputable section
namespace Catalan.A3
open UnitQuotient
variable (p q : ℕ) [Fact q.Prime]

local instance (priority := 10000) instZModSemiringPerfectKummer : Semiring (ZMod q) :=
  (inferInstance : Field (ZMod q)).toSemifield.toSemiring
local instance (priority := 10000) instZModSelfModulePerfect : Module (ZMod q) (ZMod q) :=
  Semiring.toModule
local instance (priority := 10000) instPrimePowerQuotientModulePerfect
    (B : Type*) [CommGroup B] : Module (ZMod q) (PowerQuotient B q) :=
  AddCommGroup.zmodModule (UnitQuotient.powerQuotient_exponent (B := B) q)

/-- The original relative Galois group operations, with proved commutativity. -/
@[instance_reducible]
def kummerGalCommGroup : CommGroup (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
  { (inferInstance : Group (Msub p q ≃ₐ[Bsub p q] Msub p q)) with
    mul_comm := fun σ τ => (kummerDualHom_injective p q)
      (by rw [map_mul, map_mul, mul_comm]) }

lemma kummerGal_pow_eq_one (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) : σ ^ q = 1 := by
  apply kummerDualHom_injective p q
  rw [map_pow, map_one]
  change q • kummerFunctional p q σ = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]

attribute [local instance] kummerGalCommGroup

@[instance_reducible]
def kummerGalModule : Module (ZMod q) (Additive (Msub p q ≃ₐ[Bsub p q] Msub p q)) :=
  AddCommGroup.zmodModule (fun σ => by
    change (Additive.toMul σ) ^ q = 1
    exact kummerGal_pow_eq_one p q _)

attribute [local instance] kummerGalModule

/-- The actual bilinear Kummer pairing, in the selected primitive-root coordinate. -/
def kummerPairing : Additive (Msub p q ≃ₐ[Bsub p q] Msub p q) →ₗ[ZMod q]
    Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q) :=
  ({ toFun := fun σ => kummerFunctional p q (Additive.toMul σ)
     map_zero' := kummerFunctional_one p q
     map_add' := fun σ τ => kummerFunctional_mul p q (Additive.toMul σ) (Additive.toMul τ) } :
    Additive (Msub p q ≃ₐ[Bsub p q] Msub p q) →+
      Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q)).toZModLinearMap q

lemma kummerPairing_apply (σ : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (z : PowerQuotient (𝓞 (F p))ˣ q) :
    kummerPairing p q (Additive.ofMul σ) z = kummerFunctional p q σ z := rfl

lemma kummerPairing_isPerfect : LinearMap.IsPerfPair (kummerPairing p q) := by
  apply LinearMap.IsPerfPair.of_injective'
  · intro σ τ h
    apply Additive.toMul.injective
    apply kummerDualHom_injective p q
    have hfun : kummerFunctional p q (Additive.toMul σ) =
        kummerFunctional p q (Additive.toMul τ) := by
      apply LinearMap.ext
      intro z
      have hz := congrArg (fun F : Module.Dual (ZMod q)
          (PowerQuotient (𝓞 (F p))ˣ q) => F z) h
      simpa [kummerPairing] using hz
    change Multiplicative.ofAdd (kummerFunctional p q (Additive.toMul σ)) =
      Multiplicative.ofAdd (kummerFunctional p q (Additive.toMul τ))
    exact congrArg Multiplicative.ofAdd hfun
  · apply (injective_iff_map_eq_zero (kummerPairing p q).flip).mpr
    intro z hz
    apply kummerFunctional_right_nondegenerate p q z
    intro σ
    have hzσ := LinearMap.congr_fun hz (Additive.ofMul σ)
    simpa [kummerPairing_apply] using hzσ

/-- Every functional is realized by an actual automorphism of M over B. -/
def kummerDualEquiv : Additive (Msub p q ≃ₐ[Bsub p q] Msub p q) ≃ₗ[ZMod q]
    Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q) := by
  have instPerfect : LinearMap.IsPerfPair (kummerPairing p q) := kummerPairing_isPerfect p q
  exact (kummerPairing p q).toPerfPair

lemma kummerDualEquiv_apply (σ : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (z : PowerQuotient (𝓞 (F p))ˣ q) :
    kummerDualEquiv p q (Additive.ofMul σ) z = kummerFunctional p q σ z := rfl

lemma exists_kummer_aut_of_functional
    (f : Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q)) :
    ∃ σ : Msub p q ≃ₐ[Bsub p q] Msub p q, kummerFunctional p q σ = f := by
  obtain ⟨σ, hσ⟩ := (kummerDualEquiv p q).surjective f
  refine ⟨Additive.toMul σ, ?_⟩
  apply LinearMap.ext
  intro z
  have hz := congrArg (fun F : Module.Dual (ZMod q)
      (PowerQuotient (𝓞 (F p))ˣ q) => F z) hσ
  change kummerDualEquiv p q (Additive.ofMul (Additive.toMul σ)) z = f z at hz
  simpa only [kummerDualEquiv_apply] using hz

end Catalan.A3
