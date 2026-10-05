module

public import Catalan.Mihailescu.KernelCardinality
public import Catalan.Height.LocalBounds
public import Catalan.Mihailescu.FiniteSum
public import Catalan.Mihailescu.RootPhase
public import Catalan.Mihailescu.RadiusTwoArithmetic

/-!
# `Catalan.Mihailescu.RadiusTwoHeight`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma prop42_arch_bound (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hdim : (p : ℝ) ≤ (2 - ε) * q + 1)
    (h8 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1))
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0)
    (w : InfinitePlace K) :
    (5 / 2 : ℝ) / q < w (((augAlpha p K q x hp2 Θ : Kˣ) : K) - 1) := by
  obtain ⟨hX, hr, _⟩ := h8_consequences p q hp2 x ε hε0 hε1 h8
  have hx : 1 < (|x| : ℝ) := by linarith
  have hr1 := radius_ge_one p q hp2 ε hdim
  have hs' : (size p K Θ.val : ℝ) ≤ 2 * mihRadius p q ε := by
    have hc : (size p K Θ.val : ℝ) ≤ 2 := by exact_mod_cast hs
    linarith
  let φ : K →+* ℂ := w.embedding
  let η := xi p K q x φ hp2 hx Θ
  have hη : η ≠ 1 := by
    intro h
    exact hΘ (phase_kernel p K q x hp2 hpq hq2 φ ε hε0 hε1 h8 hx Θ hs' h)
  have hb := xi_small_log p K q x φ hp2 hx (mihRadius p q ε) hr Θ hs'
  have ha : alphaC p K q x φ hp2 Θ ≠ 0 := by
    intro h
    have h' : ((augAlpha p K q x hp2 Θ : Kˣ) : K) = 0 :=
      φ.injective (by rw [map_zero]; exact h)
    exact (augAlpha p K q x hp2 Θ).ne_zero h'
  have h := root_phase_separation q hq2 (alphaC p K q x φ hp2 Θ) ha η hη
    (hb.1.trans_lt hb.2)
  rw [← InfinitePlace.norm_embedding_eq]
  simpa only [map_sub, map_one, alphaC] using h


lemma prop42_height_lt (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hdim : (p : ℝ) ≤ (2 - ε) * q + 1)
    (h8 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1))
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0) :
    logHeight ((augAlpha p K q x hp2 Θ : Kˣ) : K) <
      Real.log (0.8 * q) + Real.log (pPrime p x : ℝ) / (p - 1) := by
  let A : K := ((augAlpha p K q x hp2 Θ : Kˣ) : K)
  have hq3 : 3 ≤ q := by have := (Fact.out : q.Prime).two_le; omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hqpos : (0 : ℝ) < q := by linarith
  have harch (w : InfinitePlace K) : w ((A - 1)⁻¹) < (0.4 : ℝ) * q := by
    have hw := prop42_arch_bound p K q x hp2 hpq hq2 ε hε0 hε1 hdim h8 Θ hs hΘ w
    change (5 / 2 : ℝ) / q < w (A - 1) at hw
    have hpos : 0 < w (A - 1) := (div_pos (by norm_num) hqpos).trans hw
    rw [map_inv₀]
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hqpos).mp hw
    nlinarith
  have hf := prop42_finite_inverse_sum p K q x hp2 Θ hs hΘ
  have hh := height_lt_of_local_bounds ((A - 1)⁻¹) ((0.4 : ℝ) * q)
    (Real.log (pPrime p x : ℝ)) (by linarith) harch hf
  rw [height_inv, cyclotomic_degree p K] at hh
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [Nat.cast_sub hp1, Nat.cast_one] at hh
  have hmone : logHeight (-1 : K) = 0 := by
    exact height_root_unity (-1 : K) 2 (by norm_num) (by norm_num)
  have hsub := height_sub_le (A - 1) (-1)
  rw [hmone] at hsub
  have hrecover : A - 1 - (-1) = A := by ring
  rw [hrecover] at hsub
  have hlog : Real.log ((0.4 : ℝ) * q) + Real.log 2 = Real.log ((0.8 : ℝ) * q) := by
    rw [← Real.log_mul (by positivity : (0.4 : ℝ) * q ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  change logHeight A < _
  linarith

end Catalan
