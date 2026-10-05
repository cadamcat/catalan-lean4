module

public import Catalan.Height.Basic
public import Catalan.Mihailescu.PowerDifference
public import Catalan.Cyclotomic.Augmentation

/-!
# `Catalan.Mihailescu.ReconstructHeight`

Part of the Catalan formalization.
-/

@[expose] public section

noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma prop42_reconstruct_height (hp2 : p ≠ 2) (hx : x ≠ 0)
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0) :
    Real.log (|x| : ℝ) ≤
      (q : ℝ) * logHeight ((augAlpha p K q x hp2 Θ : Kˣ) : K) + 3 * Real.log 2 := by
  obtain ⟨σ, τ, hστ, hshape⟩ := aug_size_two_shape p K Θ.val Θ.property.2 hs hΘ
  let a : K := ((augAlpha p K q x hp2 Θ : Kˣ) : K)
  have heq : a ^ q - 1 =
      (τ (ζ p K) - σ (ζ p K)) / ((x : K) - τ (ζ p K)) := by
    simpa only [a] using prop42_power_difference p K q x hp2 Θ σ τ hshape
  have hden : (x : K) - τ (ζ p K) ≠ 0 := by
    intro hzero
    have hzero' := congrArg (fun z : K => τ.symm z) hzero
    apply x_sub_ζ_ne_zero p K x hp2
    simpa only [map_sub, map_intCast, map_zero, AlgEquiv.symm_apply_apply] using hzero'
  have hnum : τ (ζ p K) - σ (ζ p K) ≠ 0 := by
    intro hzero
    have hz : τ (ζ p K) = σ (ζ p K) := sub_eq_zero.mp hzero
    apply hστ
    apply AlgEquiv.ext
    intro z
    have hpb : σ.toAlgHom = τ.toAlgHom := by
      apply (ζ_spec p K).powerBasis ℚ |>.algHom_ext
      simpa only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_toAlgHom] using hz.symm
    have hz' := congrArg (fun f : K →ₐ[ℚ] K => f z) hpb
    simpa only [AlgEquiv.coe_toAlgHom] using hz'
  have hpow_sub : a ^ q - 1 ≠ 0 := by
    rw [heq]
    exact div_ne_zero hnum hden
  have hfrac :
      (τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1) =
        (x : K) - τ (ζ p K) := by
    rw [heq]
    field_simp [hnum, hden]
  have hxrecon : (x : K) =
      (τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1) + τ (ζ p K) := by
    rw [hfrac]
    ring
  have hτpow : (τ (ζ p K)) ^ p = 1 := by
    rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
  have hσpow : (σ (ζ p K)) ^ p = 1 := by
    rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
  have hτheight : logHeight (τ (ζ p K)) = 0 :=
    height_root_unity (τ (ζ p K)) p (Fact.out : p.Prime).pos hτpow
  have hσheight : logHeight (σ (ζ p K)) = 0 :=
    height_root_unity (σ (ζ p K)) p (Fact.out : p.Prime).pos hσpow
  have hnegpow : (-τ (ζ p K)) ^ (2 * p) = 1 := by
    rw [neg_pow, Even.neg_one_pow ⟨p, by omega⟩, one_mul]
    rw [show 2 * p = p * 2 by omega, pow_mul, hτpow, one_pow]
  have hnegheight : logHeight (-τ (ζ p K)) = 0 :=
    height_root_unity (-τ (ζ p K)) (2 * p)
      (Nat.mul_pos (by norm_num) (Fact.out : p.Prime).pos) hnegpow
  have hnum_height : logHeight (τ (ζ p K) - σ (ζ p K)) ≤ Real.log 2 := by
    simpa [hτheight, hσheight] using height_sub_le (τ (ζ p K)) (σ (ζ p K))
  have hpow_height : logHeight (a ^ q - 1) ≤
      (q : ℝ) * logHeight a + Real.log 2 := by
    calc
      logHeight (a ^ q - 1) ≤ logHeight (a ^ q) + logHeight (1 : K) + Real.log 2 :=
        height_sub_le (a ^ q) 1
      _ = (q : ℝ) * logHeight a + Real.log 2 := by
        rw [height_pow, height_one]
        ring
  have hquot_height :
      logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) ≤
        logHeight (τ (ζ p K) - σ (ζ p K)) + logHeight (a ^ q - 1) :=
    height_div_le _ _
  have hquot_bound :
      logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) ≤
        (q : ℝ) * logHeight a + 2 * Real.log 2 := by
    calc
      logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) ≤
          logHeight (τ (ζ p K) - σ (ζ p K)) + logHeight (a ^ q - 1) := hquot_height
      _ ≤ Real.log 2 + ((q : ℝ) * logHeight a + Real.log 2) :=
        add_le_add hnum_height hpow_height
      _ = (q : ℝ) * logHeight a + 2 * Real.log 2 := by ring
  have hadd_bound :
      logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1) + τ (ζ p K)) ≤
        logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) + Real.log 2 := by
    simpa [sub_neg_eq_add, hnegheight] using
      height_sub_le ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) (-τ (ζ p K))
  have hbound : logHeight (x : K) ≤
      (q : ℝ) * logHeight a + 3 * Real.log 2 := by
    rw [hxrecon]
    calc
      logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1) + τ (ζ p K)) ≤
          logHeight ((τ (ζ p K) - σ (ζ p K)) / (a ^ q - 1)) + Real.log 2 := hadd_bound
      _ ≤ ((q : ℝ) * logHeight a + 2 * Real.log 2) + Real.log 2 :=
        by linarith [hquot_bound]
      _ = (q : ℝ) * logHeight a + 3 * Real.log 2 := by ring
  rw [height_intCast x hx] at hbound
  simpa only [a] using hbound

end Catalan
