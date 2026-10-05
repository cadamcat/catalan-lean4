module

public import Catalan.Mihailescu.RadiusTwoHeight
public import Catalan.Mihailescu.ReconstructHeight
public import Catalan.Mihailescu.RadiusTwoArithmetic

/-!
# `Catalan.Mihailescu.RadiusTwoExclusion`

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

theorem aug_two_eq_zero_of_h9 (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hdim : (p : ℝ) ≤ (2 - ε) * q + 1)
    (h9 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (8 * (0.8 * q * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ))) ^ q))
    (Θ : R p K) (hΘ : Θ ∈ mihIdeal p K q x hp2)
    (hw : weight p K Θ = 0) (hs : size p K Θ ≤ 2) : Θ = 0 := by
  by_contra hne
  have h8 := h9_implies_h8 p q x hp2 hq2 ε hε0 hε1 h9
  have hX := (h8_consequences p q hp2 x ε hε0 hε1 h8).1
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hX
    norm_num at hX
  let A : mihAug p K q x hp2 := ⟨Θ, hΘ, hw⟩
  have hH := prop42_height_lt p K q x hp2 hpq hq2 ε hε0 hε1 hdim h8 A hs hne
  have hr := prop42_reconstruct_height p K q x hp2 hx A hs hne
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hn : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hP : (0 : ℝ) < pPrime p x := by exact_mod_cast pPrime_pos p x
  apply prop42_real_contradiction ((p : ℝ) - 1) (q : ℝ) (pPrime p x : ℝ)
    (|x| : ℝ) (logHeight ((augAlpha p K q x hp2 A : Kˣ) : K))
    (by linarith) hn hP (by linarith) hH hr
  have hb := (max_le_iff.mp h9).2
  simpa only [Real.rpow_natCast] using hb


theorem aug_two_eq_zero (hp2 : p ≠ 2) (hpq : p < q) (hx1 : x ≡ 1 [ZMOD p])
    (hx : (|x| : ℝ) ≥ 8 * (0.8 * q) ^ q) (Θ : R p K)
    (hΘ : Θ ∈ mihIdeal p K q x hp2)
    (hw : weight p K Θ = 0) (hs : size p K Θ ≤ 2) : Θ = 0 := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hq2 : q ≠ 2 := by omega
  have hdim : (p : ℝ) ≤ (2 - (1 : ℝ)) * q + 1 := by
    have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
    linarith
  have ht : mihThreshold p 1 ≤ (|x| : ℝ) := by
    simp only [mihThreshold, div_one, Real.rpow_one]
    exact (cor43_power_domination p q hp2 hpq).trans hx
  have hb : 8 * (0.8 * q * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ))) ^ q ≤
      (|x| : ℝ) := by
    simpa only [pPrime, if_pos hx1, Nat.cast_one, Real.one_rpow, mul_one] using hx
  exact aug_two_eq_zero_of_h9 p K q x hp2 (ne_of_lt hpq) hq2 1
    (by norm_num) (by norm_num) hdim (max_le_iff.mpr ⟨ht, hb⟩) Θ hΘ hw hs


end Catalan
