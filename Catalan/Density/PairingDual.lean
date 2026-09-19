import Catalan.Density.PairingValues
import Catalan.CaseOne.UnitCharpoly

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
open UnitQuotient
variable (p q : ℕ) [Fact q.Prime]

/-- The selected primitive root as a unit in the actual field M. -/
def kummerZetaUnitM : (Msub p q)ˣ :=
  Units.mk0 (kummerZetaM p q)
    ((kummerZetaM_spec p q (Fact.out : q.Prime).pos).ne_zero (Fact.out : q.Prime).ne_zero)

lemma kummerZetaUnitM_spec : IsPrimitiveRoot (kummerZetaUnitM p q) q :=
  IsPrimitiveRoot.coe_units_iff.mp (kummerZetaM_spec p q (Fact.out : q.Prime).pos)

def kummerCoordinate : Additive (rootsOfUnity q (Msub p q)) ≃+ ZMod q :=
  Kummer.rootsOfUnityCoordinate (Msub p q) q (kummerZetaUnitM p q) (kummerZetaUnitM_spec p q)

/-- The root-ratio map descends to the actual quotient by unit q-th powers. -/
def kummerQuotientValue (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    ((𝓞 (F p))ˣ ⧸ qPowers (𝓞 (F p))ˣ q) →* rootsOfUnity q (Msub p q) :=
  QuotientGroup.lift _ (kummerPairingHom p q σ) (by
    intro u hu
    change ∃ v : (𝓞 (F p))ˣ, v ^ q = u at hu
    obtain ⟨v, rfl⟩ := hu
    change (kummerPairingHom p q σ) (v ^ q) = 1
    rw [map_pow]
    apply Subtype.ext
    exact (kummerValue p q σ v).property)

/-- An actual linear functional on F-unit power classes. -/
def kummerFunctional (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q) :=
  ((kummerCoordinate p q).toAddMonoidHom.comp (kummerQuotientValue p q σ).toAdditive).toZModLinearMap q

lemma kummerFunctional_apply (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    kummerFunctional p q σ (powerClass q u) =
      kummerCoordinate p q (Additive.ofMul (kummerValue p q σ u)) := rfl

lemma kummerFunctional_apply_eq_zero_iff
    (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    kummerFunctional p q σ (powerClass q u) = 0 ↔ kummerValue p q σ u = 1 := by
  rw [kummerFunctional_apply]
  change kummerCoordinate p q (Additive.ofMul (kummerValue p q σ u)) = 0 ↔
    Additive.ofMul (kummerValue p q σ u) = 0
  constructor
  · intro h
    apply (kummerCoordinate p q).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

lemma kummerFunctional_one : kummerFunctional p q 1 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | _ u =>
    change kummerCoordinate p q (Additive.ofMul (kummerValue p q 1 u)) = 0
    rw [kummerValue_one_left]
    exact (kummerCoordinate p q).map_zero

lemma kummerFunctional_mul (σ τ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    kummerFunctional p q (σ * τ) = kummerFunctional p q σ + kummerFunctional p q τ := by
  apply LinearMap.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | _ u =>
    change kummerCoordinate p q (Additive.ofMul (kummerValue p q (σ * τ) u)) =
      kummerCoordinate p q (Additive.ofMul (kummerValue p q σ u)) +
        kummerCoordinate p q (Additive.ofMul (kummerValue p q τ u))
    rw [kummerValue_mul_left]
    exact (kummerCoordinate p q).map_add _ _

/-- The actual Kummer map to the dual, before its bijectivity is proved. -/
def kummerDualHom : (Msub p q ≃ₐ[Bsub p q] Msub p q) →*
    Multiplicative (Module.Dual (ZMod q) (PowerQuotient (𝓞 (F p))ˣ q)) where
  toFun σ := Multiplicative.ofAdd (kummerFunctional p q σ)
  map_one' := kummerFunctional_one p q
  map_mul' := kummerFunctional_mul p q

end Catalan.A3
