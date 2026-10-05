module

public import Catalan.CaseOne.PrimaryUnits

/-!
# `Catalan.CaseOne.PowerQuotient`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitQuotient

abbrev PowerQuotient (B : Type*) [CommGroup B] (q : ℕ) :=
  Additive (B ⧸ qPowers B q)

def powerClass {B : Type*} [CommGroup B] (q : ℕ) (b : B) : PowerQuotient B q :=
  Additive.ofMul (QuotientGroup.mk b)

lemma powerQuotient_exponent {B : Type*} [CommGroup B]
    (q : ℕ) (v : PowerQuotient B q) : q • v = 0 := by
  induction v using QuotientGroup.induction_on with
  | _ b =>
    change Additive.ofMul (QuotientGroup.mk (b ^ q)) = 0
    apply Additive.ofMul.injective
    exact (QuotientGroup.eq_one_iff (b ^ q)).mpr ⟨b, rfl⟩

noncomputable instance powerQuotientModule (B : Type*) [CommGroup B] (q : ℕ) :
    Module (ZMod q) (PowerQuotient B q) :=
  AddCommGroup.zmodModule (powerQuotient_exponent (B := B) q)

noncomputable def powerMap {B D : Type*} [CommGroup B] [CommGroup D]
    (q : ℕ) (f : B →* D) : PowerQuotient B q →ₗ[ZMod q] PowerQuotient D q := by
  have hf : qPowers B q ≤ (qPowers D q).comap f := by
    intro b hb
    change f b ∈ qPowers D q
    change ∃ a : B, a ^ q = b at hb
    obtain ⟨a, rfl⟩ := hb
    exact ⟨f a, by rw [map_pow]⟩
  let g : B ⧸ qPowers B q →* D ⧸ qPowers D q :=
    QuotientGroup.map (qPowers B q) (qPowers D q) f hf
  let ga : Additive (B ⧸ qPowers B q) →+ Additive (D ⧸ qPowers D q) :=
    { toFun := fun x => Additive.ofMul (g (Additive.toMul x))
      map_zero' := by
        change g 1 = 1
        exact g.map_one
      map_add' := by
        intro x y
        change g ((Additive.toMul x) * (Additive.toMul y)) =
          g (Additive.toMul x) * g (Additive.toMul y)
        exact g.map_mul _ _ }
  exact ga.toZModLinearMap q

lemma powerMap_apply {B D : Type*} [CommGroup B] [CommGroup D]
    (q : ℕ) (f : B →* D) (b : B) :
    powerMap q f (powerClass q b) = powerClass q (f b) := by
  rfl

end Catalan.UnitQuotient
