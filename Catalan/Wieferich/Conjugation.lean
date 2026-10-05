module

public import Catalan.Wieferich.Defs
public import Mathlib

/-!
# `Catalan.Wieferich.Conjugation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma iota_on_embeddings (hp2 : p ≠ 2) (φ : K →+* ℂ) (a : K) :
    φ (ι p K a) = conj (φ a) := by
  have hpgt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  have hiota : ι p K (ζ p K) = (ζ p K)⁻¹ := by
    rw [ι, σ_apply_ζ]
    have hn : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
      change (-1 : ZMod p).val = p - 1
      have hvalone : (1 : ZMod p).val = 1 := by
        rw [ZMod.val_one_eq_one_mod]
        exact Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt
      calc
        (-1 : ZMod p).val = p - (1 : ZMod p).val := by
          have h := ZMod.neg_val (1 : ZMod p)
          rw [if_neg (one_ne_zero : (1 : ZMod p) ≠ 0)] at h
          exact h
        _ = p - 1 := by rw [hvalone]
    rw [hn]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p),
      (ζ_spec p K).pow_eq_one]
  let f : K →ₐ[ℚ] ℂ := φ.toRatAlgHom.comp (ι p K).toAlgHom
  let g : K →ₐ[ℚ] ℂ :=
    (Complex.conjAe.toRingEquiv.toRingHom.comp φ).toRatAlgHom
  have hfg : f = g := by
    apply (ζ_spec p K).powerBasis ℚ |>.algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    dsimp [f, g]
    rw [hiota]
    rw [map_inv₀]
    have hpow : (φ (ζ p K)) ^ p = 1 := by
      rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
    rw [← Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hpow
      (Fact.out : p.Prime).ne_zero)]
  have hfg_a := congrArg (fun h : K →ₐ[ℚ] ℂ => h a) hfg
  exact hfg_a

lemma torsion_order_bound (hp2 : p ≠ 2) (t : Kˣ)
    (ht : ∃ n : ℕ, 0 < n ∧ t ^ n = 1) : t ^ (2 * p) = 1 := by
  have hpgt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  have ht' : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr ht
  have htK : IsOfFinOrder (t : K) := Units.isOfFinOrder_val.mpr ht'
  have hord : orderOf (t : K) ≠ 0 := orderOf_ne_zero_iff.mpr htK
  have hdiv : orderOf (t : K) ∣ 2 * p := by
    exact (IsPrimitiveRoot.orderOf (t : K)).dvd_of_isCyclotomicExtension p hord
  apply Units.ext
  exact (orderOf_dvd_iff_pow_eq_one.mp hdiv)

end Catalan.A1e
