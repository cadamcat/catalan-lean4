import Catalan.Mihailescu.FiniteValues
import Catalan.Mihailescu.PowerDifference
import Catalan.Mihailescu.NearOne
import Catalan.Cyclotomic.Augmentation

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma prop42_finite_lower (hp2 : p ≠ 2)
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0)
    (v : FinitePlace K) :
    (v (pPrime p x : K)) ^ (1 / (p - 1 : ℝ)) ≤
      v (((augAlpha p K q x hp2 Θ : Kˣ) : K) - 1) := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hpn : p - 1 ≠ 0 := by omega
  have hpR : 0 < (p : ℝ) - 1 := by exact_mod_cast (show 0 < (p : ℤ) - 1 by omega)
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
  let a : K := ((augAlpha p K q x hp2 Θ : Kˣ) : K)
  change (v (pPrime p x : K)) ^ (1 / (p - 1 : ℝ)) ≤ v (a - 1)
  have hpp : v (pPrime p x : K) ≤ 1 := by
    simpa using finitePlace_integral_le_one K v (pPrime p x : 𝓞 K)
  by_cases ha : v (a - 1) < 1
  · obtain ⟨σ, τ, hστ, hshape⟩ := aug_size_two_shape p K Θ.val Θ.property.2 hs hΘ
    have hden0 : (x : K) - τ (ζ p K) ≠ 0 := by
      intro hzero
      have hzero' := congrArg (fun z : K => τ.symm z) hzero
      apply x_sub_ζ_ne_zero p K x hp2
      simpa only [map_sub, map_intCast, map_zero, AlgEquiv.symm_apply_apply] using hzero'
    have hdpos : 0 < v ((x : K) - τ (ζ p K)) := FinitePlace.pos_iff.mpr hden0
    have hdle : v ((x : K) - τ (ζ p K)) ≤ 1 := by
      have hh := finitePlace_integral_le_one K v ((x : 𝓞 K) - zetaConjInt p K τ)
      change v ((x : K) - τ (ζ p K)) ≤ 1 at hh
      exact hh
    have heq : a ^ q - 1 = (τ (ζ p K) - σ (ζ p K)) / ((x : K) - τ (ζ p K)) :=
      prop42_power_difference p K q x hp2 Θ σ τ hshape
    have hnear := finite_power_near_one K q v a ha
    rw [heq, map_div₀] at hnear
    have hnumle : v (τ (ζ p K) - σ (ζ p K)) ≤ v (a - 1) := by
      apply le_trans _ hnear
      apply (le_div_iff₀ hdpos).mpr
      exact mul_le_of_le_one_right (apply_nonneg v _) hdle
    have hnum : v (τ (ζ p K) - σ (ζ p K)) ^ (p - 1) = v (p : K) :=
      finitePlace_root_difference_pow p K hp2 v σ τ hστ
    by_cases hx1 : x ≡ 1 [ZMOD p]
    · have ht : v (τ (ζ p K) - σ (ζ p K)) = v (1 - τ (ζ p K)) := by
        apply (pow_left_inj₀ (apply_nonneg v _) (apply_nonneg v _) hpn).mp
        rw [hnum, finitePlace_root_distance_pow]
      have ht0 : 0 < v (1 - τ (ζ p K)) := by
        apply FinitePlace.pos_iff.mpr
        exact sub_ne_zero.mpr
          (((ζ_spec p K).map_of_injective τ.injective).ne_one (Fact.out : p.Prime).one_lt).symm
      have ht1 : v (1 - τ (ζ p K)) < 1 := by
        rw [ht] at hnumle
        exact hnumle.trans_lt ha
      have hplt : v (p : K) < v (1 - τ (ζ p K)) := by
        rw [← finitePlace_root_distance_pow p K v τ]
        exact pow_lt_self_of_lt_one₀ ht0 ht1 (by omega)
      have hdiv : (p : 𝓞 K) ∣ (x : 𝓞 K) - 1 := by
        obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hx1.symm
        refine ⟨(k : 𝓞 K), ?_⟩
        exact_mod_cast hk
      have hxv : v ((x : K) - 1) ≤ v (p : K) := by
        simpa using finitePlace_le_of_dvd K v (p : 𝓞 K) ((x : 𝓞 K) - 1) hdiv
      have hd : v ((x : K) - τ (ζ p K)) = v (1 - τ (ζ p K)) := by
        have hid : (x : K) - τ (ζ p K) = ((x : K) - 1) + (1 - τ (ζ p K)) := by ring
        rw [hid]
        exact IsNonarchimedean.add_eq_right_of_lt (fun y z => v.add_le y z) (hxv.trans_lt hplt)
      rw [ht, hd, div_self ht0.ne'] at hnear
      exact (not_lt_of_ge hnear ha).elim
    · rw [pPrime, if_neg hx1]
      have hroot : (v (p : K)) ^ (1 / (p - 1 : ℝ)) =
          v (τ (ζ p K) - σ (ζ p K)) := by
        rw [← hnum, ← hcast, one_div]
        exact Real.pow_rpow_inv_natCast (apply_nonneg v _) hpn
      rw [hroot]
      exact hnumle
  · apply le_trans _ (le_of_not_gt ha)
    exact Real.rpow_le_one (apply_nonneg v _) hpp (le_of_lt (one_div_pos.mpr hpR))

end Catalan

