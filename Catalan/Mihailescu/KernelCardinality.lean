import Catalan.Mihailescu.GroupRingHeight
import Catalan.Height.Liouville
import Catalan.Mihailescu.PhaseBounds
import Catalan.Mihailescu.Threshold
import Catalan.Mihailescu.RealContradiction
import Catalan.Mihailescu.ExpBound
import Catalan.Mihailescu.Separation
import Catalan.Counting.SmallBall

noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma phase_kernel (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (φ : K →+* ℂ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h8 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1))
    (hx : 1 < (|x| : ℝ)) (Θ : mihAug p K q x hp2)
    (hs : (size p K Θ.val : ℝ) ≤ 2 * mihRadius p q ε)
    (hξ : xi p K q x φ hp2 hx Θ = 1) : Θ.val = 0 := by
  by_contra hΘ
  obtain ⟨hX, hr, ht⟩ := h8_consequences p q hp2 x ε hε0 hε1 h8
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hd : 2 ≤ p - 1 := by omega
  have hdcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hs0 : (0 : ℝ) < size p K Θ.val := by
    have hn := size_nonneg p K Θ.val
    have hz : size p K Θ.val ≠ 0 := by
      intro hz; exact hΘ ((size_eq_zero_iff p K Θ.val).mp hz)
    exact_mod_cast (lt_of_le_of_ne hn (Ne.symm hz))
  let A : Kˣ := augAlpha p K q x hp2 Θ
  have hAunit : A ≠ 1 := by
    apply alpha_ne_one p K q x hp2
    · exact_mod_cast (show (2 : ℝ) ≤ (|x| : ℝ) by linarith)
    · intro _ heq
      have hX' := hX
      rw [heq] at hX'
      norm_num at hX'
    · exact hΘ
  have hA : (A : K) ≠ 1 := by
    intro ha; exact hAunit (Units.ext ha)
  have hAc : φ (A : K) ≠ 0 := by
    intro ha
    have : (A : K) = 0 := φ.injective (by rw [map_zero]; exact ha)
    exact A.ne_zero this
  have hb := (xi_small_log p K q x φ hp2 hx (mihRadius p q ε) hr Θ hs).1
  have hlog : ‖Complex.log (φ (A : K))‖ ≤
      (size p K Θ.val : ℝ) / ((q : ℝ) * ((|x| : ℝ) - 1)) := by
    simpa only [hξ, OneMemClass.coe_one, Units.val_one, div_one, alphaC] using hb
  have hrat := small_ratio_le ((p : ℝ) - 1) (q : ℝ) (|x| : ℝ) ε
    (size p K Θ.val : ℝ) (by
      have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith) hq0 hX hε0 (le_of_lt hs0) hs
  have hlogπ : ‖Complex.log (φ (A : K))‖ ≤ Real.pi / 5 := by
    have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hU : ‖φ ((A : K) - 1)‖ ≤ (7 / 5 : ℝ) *
      ((size p K Θ.val : ℝ) / ((q : ℝ) * ((|x| : ℝ) - 1))) := by
    rw [map_sub, map_one, ← Complex.exp_log hAc]
    exact (expm1_seven_fifths _ hlogπ).trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
  have hHa := prop47_height p K q x hp2 ⟨Θ.val, Θ.property.1⟩
  have hw : weight p K Θ.val = 0 := Θ.property.2
  simp only [hw, Int.cast_zero, abs_zero, add_zero] at hHa
  have hH : logHeight ((A : K) - 1) ≤
      (size p K Θ.val : ℝ) / (2 * (q : ℝ)) * Real.log ((|x| : ℝ) + 1) +
        Real.log 2 := by
    have h := height_sub_le (A : K) 1
    rw [height_one] at h
    change logHeight (A : K) ≤ _ at hHa
    linarith
  have hL := height_liouville_complex φ (embedding_isComplex p K hp2 φ)
    ((A : K) - 1) (sub_ne_zero.mpr hA)
  rw [cyclotomic_degree p K] at hL
  apply prop49_real_contradiction (p - 1) hd (q : ℝ) (|x| : ℝ) ε
    (size p K Θ.val : ℝ) (logHeight ((A : K) - 1)) ‖φ ((A : K) - 1)‖
    hq0 hX hε0 hε1 hs0
  · simpa only [hdcast, mihRadius] using hs
  · simpa only [hdcast] using ht
  · exact hH
  · exact norm_nonneg _
  · exact hU
  · exact hL

lemma phase_injective_ball (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (φ : K →+* ℂ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h8 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1)) (hx : 1 < (|x| : ℝ)) :
    Function.Injective (fun Θ : augBall p K q x hp2 (mihRadius p q ε) =>
      xi p K q x φ hp2 hx ⟨Θ.val, Θ.property.1, Θ.property.2.1⟩) := by
  intro Θ Ψ heq
  let A : mihAug p K q x hp2 := ⟨Θ.val, Θ.property.1, Θ.property.2.1⟩
  let B : mihAug p K q x hp2 := ⟨Ψ.val, Ψ.property.1, Ψ.property.2.1⟩
  have hs : (size p K (A - B).val : ℝ) ≤ 2 * mihRadius p q ε := by
    have h := size_sub_le p K Θ.val Ψ.val
    have hc : (size p K (Θ.val - Ψ.val) : ℝ) ≤
        (size p K Θ.val : ℝ) + (size p K Ψ.val : ℝ) := by exact_mod_cast h
    have hΘ := Θ.property.2.2
    have hΨ := Ψ.property.2.2
    change (size p K (Θ.val - Ψ.val) : ℝ) ≤ _
    linarith
  have hξ : xi p K q x φ hp2 hx (A - B) = 1 := by
    rw [xi_sub p K q x φ hp2 hpq hq2 hx]
    change xi p K q x φ hp2 hx A = xi p K q x φ hp2 hx B at heq
    rw [heq, div_self']
  have hz := phase_kernel p K q x hp2 hpq hq2 φ ε hε0 hε1 h8 hx (A - B) hs hξ
  apply Subtype.ext
  exact sub_eq_zero.mp hz

/-- Bilu (2005), Theorem 4.1. The frozen statement, including its q=2 case. -/
theorem card_aug_ball_le (hp2 : p ≠ 2) (hpq : p ≠ q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h8 : (|x| : ℝ) ≥ max ((36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2)) ^ (1 / ε))
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1)) :
    Set.ncard {Θ ∈ mihIdeal p K q x hp2 | weight p K Θ = 0 ∧
      (size p K Θ : ℝ) ≤ (2 - ε) * q / (p - 1)} ≤ q := by
  classical
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  by_cases hqp : q < p
  · have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    have hqp' : (q : ℝ) ≤ (p : ℝ) - 1 := by
      have h : (q : ℝ) + 1 ≤ p := by exact_mod_cast (show q + 1 ≤ p by omega)
      linarith
    have hr : (2 - ε) * q / (p - 1 : ℝ) < 2 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith [mul_pos hε0 hq0]
    have hsub : {Θ ∈ mihIdeal p K q x hp2 | weight p K Θ = 0 ∧
        (size p K Θ : ℝ) ≤ (2 - ε) * q / (p - 1)} ⊆ {0} := by
      intro Θ hΘ
      exact Set.mem_singleton_iff.mpr
        (aug_size_lt_two p K Θ hΘ.2.1 (hΘ.2.2.trans_lt hr))
    calc
      _ ≤ Set.ncard ({0} : Set (R p K)) :=
        Set.ncard_le_ncard hsub (Set.finite_singleton 0)
      _ = 1 := Set.ncard_singleton _
      _ ≤ q := (Fact.out : q.Prime).one_le
  · have hpq' : p < q := by omega
    have hq2 : q ≠ 2 := by omega
    have h8' : (|x| : ℝ) ≥ max (mihThreshold p ε)
        (4 / Real.pi * (q : ℝ) / (p - 1) + 1) := h8
    have hx : 1 < (|x| : ℝ) := by
      have hX := (h8_consequences p q hp2 x ε hε0 hε1 h8').1
      linarith
    let φ : K →+* ℂ := (Classical.choice (inferInstance : Nonempty (InfinitePlace K))).embedding
    let S := augBall p K q x hp2 (mihRadius p q ε)
    let instKernelBallFintype : Fintype S := (finite_aug_ball p K q x hp2 (mihRadius p q ε)).fintype
    let instKernelRootsFintype : Fintype (rootsOfUnity q ℂ) := Fintype.ofFinite _
    change Set.ncard S ≤ q
    rw [← Set.fintypeCard_eq_ncard]
    calc
      Fintype.card S ≤ Fintype.card (rootsOfUnity q ℂ) :=
        Fintype.card_le_of_injective _
          (phase_injective_ball p K q x hp2 hpq hq2 φ ε hε0 hε1 h8' hx)
      _ = Nat.card (rootsOfUnity q ℂ) := (Nat.card_eq_fintype_card).symm
      _ ≤ q := card_rootsOfUnity (k := q) (R := ℂ)


end Catalan
