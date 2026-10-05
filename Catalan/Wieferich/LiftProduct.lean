module

public import Catalan.Wieferich.Core
public import Catalan.Wieferich.Action
public import Catalan.Wieferich.Coefficient

/-!
# `Catalan.Wieferich.LiftProduct`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma liftProduct_qth
    (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (x : ℤ)
    (hpow : ∃ b : Kˣ,
      upow p K (xmζ p K x hp2) (testTheta p K) = b ^ q) :
    ∃ b : K, b ^ q = (liftProduct p K q x : K)
 := by
  classical
  let liftProductFintypeG : Fintype (G p K) := Fintype.ofFinite _
  have hz0 : ζ p K ≠ 0 := (ζ_spec p K).ne_zero (Fact.out : p.Prime).ne_zero
  let ρ : Kˣ := Units.mk0 (-ζ p K) (neg_ne_zero.mpr hz0)
  let u : Kˣ := xmζ p K x hp2 / ρ
  let T := testTheta p K
  have hρ : ρ ^ (2 * p) = 1 := by
    apply Units.ext
    change (-ζ p K) ^ (2 * p) = (1 : K)
    rw [pow_mul, neg_sq, ← pow_mul, mul_comm 2 p, pow_mul,
      (ζ_spec p K).pow_eq_one, one_pow]
  have hcop : Nat.Coprime q (2 * p) :=
    ((Nat.coprime_primes hq Nat.prime_two).mpr hq2).mul_right
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).mpr hpq.symm)
  obtain ⟨w, hw⟩ := qth_root_of_coprime (upow p K ρ T) (2 * p) q
    (upow_pow_eq_one p K ρ T (2 * p) hρ) hcop
  obtain ⟨b, hb⟩ := hpow
  have hub : upow p K u T = (b / w) ^ q := by
    change upow p K (xmζ p K x hp2 / ρ) (testTheta p K) = _
    rw [upow_base_div, hb, ← hw, div_pow]
  have hu : (u : K) = 1 - (x : K) * (ζ p K)⁻¹ := by
    dsimp only [u]
    rw [Units.val_div_eq_div_val]
    change ((x : K) - ζ p K) / (-ζ p K) = _
    field_simp [hz0]
    ring
  have hinvζ : (ζ p K) ^ (p - 1) = (ζ p K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
      (ζ_spec p K).pow_eq_one]
  have hic (a : (ZMod p)ˣ) : (inverseConjugate p K a : K) =
      (σ p K a)⁻¹ ((ζ p K)⁻¹) := by
    change (σ p K a)⁻¹ ((ζ p K) ^ (p - 1)) = _
    rw [hinvζ]
  let f : (ZMod p)ˣ → Kˣ := fun a => actUnit p K (σ p K a)⁻¹ u
  have hf (a : (ZMod p)ˣ) : (f a : K) =
      ((1 - (x : 𝓞 K) * inverseConjugate p K a : 𝓞 K) : K) := by
    change (σ p K a)⁻¹ (u : K) = 1 - (x : K) * (inverseConjugate p K a : K)
    rw [hu, map_sub, map_one, map_mul, map_intCast, hic]
  have hprod : (∏ a : (ZMod p)ˣ, (f a) ^ (T.coeff ((σ p K a)⁻¹))) = upow p K u T := by
    rw [upow_fintype]
    exact ((Equiv.inv (G p K)).bijective.comp (σ_bijective p K)).prod_comp
      (fun τ => (actUnit p K τ u) ^ (T.coeff τ))
  let D : Kˣ := ∏ a : (ZMod p)ˣ, if 2 * (a : ZMod p).val < p then f a else 1
  have hq2one : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  have hfactor (a : (ZMod p)ˣ) :
      f a ^ liftCoefficient p q a = f a ^ (T.coeff ((σ p K a)⁻¹)) *
        (if 2 * (a : ZMod p).val < p then f a else 1) ^ (q ^ 2) := by
    dsimp only [T]
    rw [testTheta_coefficient p K hp2]
    unfold liftCoefficient
    split_ifs with h
    · calc
        f a ^ (q ^ 2 - 1) = f a ^ ((q ^ 2 : ℤ) - 1) := by
          rw [← zpow_natCast, Nat.cast_sub hq2one, Nat.cast_one, Nat.cast_pow]
        _ = f a ^ (-1 : ℤ) * f a ^ (q ^ 2) := by
          rw [zpow_sub, zpow_one, zpow_neg_one, ← zpow_natCast]
          push_cast
          simp only [mul_comm]
    · simp only [pow_one, zpow_one, one_pow, mul_one]
  have hlift : (∏ a : (ZMod p)ˣ, f a ^ liftCoefficient p q a) = ((b / w) * D ^ q) ^ q := by
    calc
      (∏ a : (ZMod p)ˣ, f a ^ liftCoefficient p q a) =
          (∏ a : (ZMod p)ˣ, f a ^ (T.coeff ((σ p K a)⁻¹))) * D ^ (q ^ 2) := by
        simp only [D, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun a _ => hfactor a)
      _ = (b / w) ^ q * (D ^ q) ^ q := by
        rw [hprod, hub, ← pow_mul, pow_two]
      _ = ((b / w) * D ^ q) ^ q := (mul_pow _ _ _).symm
  refine ⟨(((b / w) * D ^ q : Kˣ) : K), ?_⟩
  have hcoelift : (((∏ a : (ZMod p)ˣ, f a ^ liftCoefficient p q a) : Kˣ) : K) =
      (liftProduct p K q x : K) := by
    change (Units.coeHom K) (∏ a : (ZMod p)ˣ, f a ^ liftCoefficient p q a) =
      (algebraMap (𝓞 K) K) (∏ a : (ZMod p)ˣ,
        (1 - (x : 𝓞 K) * inverseConjugate p K a) ^ liftCoefficient p q a)
    rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [map_pow, map_pow]
    exact congrArg (fun z : K => z ^ liftCoefficient p q a) (hf a)
  rw [← hcoelift, hlift, Units.val_pow_eq_pow_val]

end Catalan.A1e

