module

public import Catalan.Stickelberger.CyclotomicLift
public import Mathlib.Data.ZMod.Units

/-!
# `Catalan.Stickelberger.TowerLift`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan

 theorem exists_cyclotomic_tower_lift
    (p ell m N : ℕ) [Fact p.Prime] [NeZero ell] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L]
    [IsCyclotomicExtension {p} ℚ K] [IsCyclotomicExtension {N} ℚ L]
    (hN : N = ell * m) (hcop : ell.Coprime m) (hpm : p ∣ m)
    {z : L} (hz : IsPrimitiveRoot z ell) (a : (ZMod p)ˣ) :
    ∃ s : L ≃+* L, s z = z ∧
      ∀ x : K, s (algebraMap K L x) = algebraMap K L (σ p K a x) := by
  subst N
  have instLocal1 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨c, hc⟩ := ZMod.unitsMap_surjective hpm a
  have hcp : (c : ZMod m).val % p = (a : ZMod p).val := by
    have hc' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hc
    rw [ZMod.unitsMap_val] at hc'
    simpa only [ZMod.cast_eq_val, ZMod.val_natCast] using congrArg ZMod.val hc'
  let b := Nat.chineseRemainder hcop 1 (c : ZMod m).val
  have hbe : b.val.Coprime ell := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.1,
      ZMod.coprime_mod_iff_coprime]
    exact Nat.coprime_one_left ell
  have hbm : b.val.Coprime m := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.2,
      ZMod.coprime_mod_iff_coprime]
    exact ZMod.val_coe_unit_coprime c
  have hbp : b.val % p = (a : ZMod p).val := by
    calc
      b.val % p = (b.val % m) % p := (Nat.mod_mod_of_dvd b.val hpm).symm
      _ = ((c : ZMod m).val % m) % p := congrArg (· % p) b.prop.2
      _ = (c : ZMod m).val % p := Nat.mod_mod_of_dvd _ hpm
      _ = (a : ZMod p).val := hcp
  let u : (ZMod (ell * m))ˣ := ZMod.unitOfCoprime b.val (hbe.mul_right hbm)
  let s := (IsCyclotomicExtension.Rat.galEquivZMod (ell * m) L).symm u
  have hs (x : L) (hx : x ^ (ell * m) = 1) : s x = x ^ b.val := by
    have hs := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (ell * m) L s hx
    simp only [s, MulEquiv.apply_symm_apply, u, ZMod.coe_unitOfCoprime,
      ZMod.val_natCast] at hs
    exact hs.trans (pow_eq_pow_mod b.val hx).symm
  refine ⟨s.toRingEquiv, ?_, ?_⟩
  · change s z = z
    rw [hs _ (by rw [pow_mul, hz.pow_eq_one, one_pow]),
      pow_eq_pow_mod b.val hz.pow_eq_one, b.prop.1,
      ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one]
  · have heq : s.toAlgHom.comp (IsScalarTower.toAlgHom ℚ K L) =
        (IsScalarTower.toAlgHom ℚ K L).comp (σ p K a).toAlgHom := by
      apply (ζ_spec p K).powerBasis ℚ |>.algHom_ext
      simp only [IsPrimitiveRoot.powerBasis_gen, AlgHom.comp_apply,
        AlgEquiv.coe_toAlgHom, IsScalarTower.toAlgHom_apply, σ_apply_ζ, map_pow]
      have hm : (algebraMap K L (ζ p K)) ^ p = 1 := by
        rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
      have hroot : (algebraMap K L (ζ p K)) ^ (ell * m) = 1 := by
        obtain ⟨k, hk⟩ := hpm
        rw [hk, ← mul_assoc, mul_comm ell p, mul_assoc, pow_mul, hm, one_pow]
      rw [hs _ hroot, pow_eq_pow_mod b.val hm, hbp]
    intro x
    exact DFunLike.congr_fun heq x

end Catalan

