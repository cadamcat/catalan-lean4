import Catalan.CaseOne.PowerQuotient

set_option autoImplicit false
noncomputable section
namespace Catalan.Residue
open UnitQuotient
variable {B : Type*} [CommGroup B] (q : ℕ)

lemma coordinate_zpow
    (e : PowerQuotient B q ≃ₗ[ZMod q] ZMod q) (s : B)
    (hs : e (powerClass q s) = 1) (m : ℤ) :
    e (powerClass q (s ^ m)) = (m : ZMod q) := by
  have hpow : powerClass q (s ^ m) = m • powerClass q s :=
    (QuotientGroup.mk' (qPowers B q)).toAdditive.map_zsmul m (Additive.ofMul s)
  rw [hpow, map_zsmul, hs, zsmul_eq_mul, mul_one]

lemma coordinate_eq_iff_power_error
    (e : PowerQuotient B q ≃ₗ[ZMod q] ZMod q) (s : B)
    (hs : e (powerClass q s) = 1) (x : B) (m : ℤ) :
    e (powerClass q x) = (m : ZMod q) ↔ ∃ w : B, x = s ^ m * w ^ q := by
  constructor
  · intro hx
    have heq : powerClass q x = powerClass q (s ^ m) :=
      e.injective (hx.trans (coordinate_zpow q e s hs m).symm)
    change (QuotientGroup.mk x : B ⧸ qPowers B q) = QuotientGroup.mk (s ^ m) at heq
    obtain ⟨w, hw⟩ : ∃ w : B, w ^ q = x / s ^ m :=
      QuotientGroup.eq_iff_div_mem.mp heq
    exact ⟨w, by rw [hw]; simp⟩
  · rintro ⟨w, hw⟩
    have heq : (QuotientGroup.mk x : B ⧸ qPowers B q) = QuotientGroup.mk (s ^ m) :=
      QuotientGroup.eq_iff_div_mem.mpr ⟨w, by rw [hw]; simp⟩
    have hclass : powerClass q x = powerClass q (s ^ m) := heq
    rw [hclass, coordinate_zpow q e s hs m]

end Catalan.Residue
