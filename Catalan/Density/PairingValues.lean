import Catalan.Density.KummerTower
import Catalan.Density.RootRatio
import Catalan.Density.RootCoordinates

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]

private lemma unitRoot_pow_B (u : (𝓞 (F p))ˣ) :
    unitRoot p q (Fact.out : q.Prime).pos u ^ q =
      algebraMap (Bsub p q) (Msub p q) (algebraMap (F p) (Bsub p q) ((u : 𝓞 (F p)) : F p)) := by
  rw [← IsScalarTower.algebraMap_apply, unitRoot_pow]

/-- The actual automorphism/root ratio for a global unit of F. -/
def kummerValue (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    rootsOfUnity q (Msub p q) :=
  rootsOfUnity.mkOfPowEq
    (σ (unitRoot p q (Fact.out : q.Prime).pos u) /
      unitRoot p q (Fact.out : q.Prime).pos u) (by
    rw [div_pow, ← map_pow, unitRoot_pow_B, σ.commutes]
    exact div_self (by
      rw [← unitRoot_pow_B]
      exact pow_ne_zero q (unitRoot_ne_zero p q (Fact.out : q.Prime).pos u)))

lemma kummerValue_val (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    (((kummerValue p q σ u : rootsOfUnity q (Msub p q)) : (Msub p q)ˣ) : Msub p q) =
      σ (unitRoot p q (Fact.out : q.Prime).pos u) /
        unitRoot p q (Fact.out : q.Prime).pos u := rfl

lemma kummerValue_eq_one_iff (σ : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (u : (𝓞 (F p))ˣ) : kummerValue p q σ u = 1 ↔
      σ (unitRoot p q (Fact.out : q.Prime).pos u) =
        unitRoot p q (Fact.out : q.Prime).pos u := by
  rw [Subtype.ext_iff, Units.ext_iff]
  change σ (unitRoot p q (Fact.out : q.Prime).pos u) /
    unitRoot p q (Fact.out : q.Prime).pos u = 1 ↔ _
  exact div_eq_one_iff_eq (unitRoot_ne_zero p q (Fact.out : q.Prime).pos u)

lemma kummerValue_mul_left (σ τ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    kummerValue p q (σ * τ) u = kummerValue p q σ u * kummerValue p q τ u := by
  apply Subtype.ext
  apply Units.ext
  change (σ * τ) (unitRoot p q (Fact.out : q.Prime).pos u) /
      unitRoot p q (Fact.out : q.Prime).pos u = _
  exact Kummer.root_ratio_aut_mul (Bsub p q) (Msub p q) q (kummerZeta p q)
    (kummerZeta_spec p q (Fact.out : q.Prime).pos) σ τ _
    (unitRoot_ne_zero p q (Fact.out : q.Prime).pos u) _ (unitRoot_pow_B p q u)

lemma kummerValue_mul_right (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u v : (𝓞 (F p))ˣ) :
    kummerValue p q σ (u * v) = kummerValue p q σ u * kummerValue p q σ v := by
  let hq := (Fact.out : q.Prime).pos
  have hpow : unitRoot p q hq (u * v) ^ q =
      (unitRoot p q hq u * unitRoot p q hq v) ^ q := by
    rw [mul_pow, unitRoot_pow, unitRoot_pow, unitRoot_pow]
    simp
  have hr := Kummer.root_ratio_independent (Bsub p q) (Msub p q) q (kummerZeta p q)
    (kummerZeta_spec p q hq) σ _ _ (unitRoot_ne_zero p q hq (u * v))
    (mul_ne_zero (unitRoot_ne_zero p q hq u) (unitRoot_ne_zero p q hq v)) hpow
  apply Subtype.ext
  apply Units.ext
  change σ (unitRoot p q hq (u * v)) / unitRoot p q hq (u * v) =
    (σ (unitRoot p q hq u) / unitRoot p q hq u) *
      (σ (unitRoot p q hq v) / unitRoot p q hq v)
  rw [hr, map_mul]
  exact mul_div_mul_comm _ _ _ _

lemma kummerValue_one_right (σ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    kummerValue p q σ 1 = 1 := by
  apply mul_left_cancel (a := kummerValue p q σ 1)
  rw [← kummerValue_mul_right, one_mul, mul_one]

lemma kummerValue_one_left (u : (𝓞 (F p))ˣ) : kummerValue p q 1 u = 1 := by
  apply Subtype.ext
  apply Units.ext
  change unitRoot p q (Fact.out : q.Prime).pos u /
    unitRoot p q (Fact.out : q.Prime).pos u = 1
  exact div_self (unitRoot_ne_zero p q (Fact.out : q.Prime).pos u)

/-- A pairing homomorphism before asserting commutativity of the Galois group. -/
def kummerPairingHom : (Msub p q ≃ₐ[Bsub p q] Msub p q) →*
    ((𝓞 (F p))ˣ →* rootsOfUnity q (Msub p q)) where
  toFun σ :=
    { toFun := kummerValue p q σ
      map_one' := kummerValue_one_right p q σ
      map_mul' := kummerValue_mul_right p q σ }
  map_one' := by
    apply MonoidHom.ext
    intro u
    exact kummerValue_one_left p q u
  map_mul' σ τ := by
    apply MonoidHom.ext
    intro u
    exact kummerValue_mul_left p q σ τ u

end Catalan.A3
