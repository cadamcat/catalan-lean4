module

public import Catalan.Counting.ThetaCombination
public import Catalan.Counting.Defs
public import Catalan.Stickelberger.MinusMihailescu

/-!
# `Catalan.Counting.CoefficientBall`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime]

lemma thetaCombination_mem_mihIdeal
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (c : Fin ((p - 1) / 2) → ℤ) :
    thetaCombination p K c ∈ mihIdeal p K q x hp2 := by
  let I := mihIdeal p K q x hp2
  have hθ (i : Fin ((p - 1) / 2)) :
      θminus p K (i.val + 1) ∈ I := by
    exact θminus_mem_mihIdeal p K q hp2 hq2 x y hx hy h (i.val + 1)
  unfold thetaCombination
  induction (Finset.univ : Finset (Fin ((p - 1) / 2))) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact I.zero_mem
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply I.add_mem
      · exact I.toAddSubgroup.zsmul_mem (hθ i) (c i)
      · exact ih

lemma thetaCombination_mem_augBall
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (r : ℕ) (c : Fin ((p - 1) / 2) → ℤ)
    (hc : ∑ i, |c i| ≤ (r : ℤ)) :
    thetaCombination p K c ∈ augBall p K q x hp2 (((p : ℝ) - 1) * (r : ℝ)) := by
  refine ⟨thetaCombination_mem_mihIdeal p K q hp2 hq2 x y hx hy h c,
    thetaCombination_weight p K c, ?_⟩
  have hsize := thetaCombination_size p K c
  have hsizeR : (size p K (thetaCombination p K c) : ℝ) ≤
      ((((p : ℤ) - 1) * ∑ i, |c i| : ℤ) : ℝ) := by
    exact_mod_cast hsize
  have hcR : ((∑ i, |c i| : ℤ) : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hc
  have hpR : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have hpR0 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast ((Fact.out : p.Prime).one_lt.le)
    linarith
  have hprod :
      ((((p : ℤ) - 1) * ∑ i, |c i| : ℤ) : ℝ) ≤
        ((p : ℝ) - 1) * (r : ℝ) := by
    calc
      ((((p : ℤ) - 1) * ∑ i, |c i| : ℤ) : ℝ) =
          ((p : ℝ) - 1) * ((∑ i, |c i| : ℤ) : ℝ) := by norm_num
      _ ≤ ((p : ℝ) - 1) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hcR hpR
  exact hsizeR.trans hprod

lemma S_le_card_augBall
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (r : ℕ) :
    S ((p - 1) / 2) r ≤
      (augBall p K q x hp2 (((p : ℝ) - 1) * (r : ℝ))).ncard := by
  let C : Set (Fin ((p - 1) / 2) → ℤ) :=
    {c | ∑ i, |c i| ≤ (r : ℤ)}
  let A : Set (R p K) := augBall p K q x hp2 (((p : ℝ) - 1) * (r : ℝ))
  have hA : A.Finite := finite_aug_ball p K q x hp2 _
  have hC : C.Finite := LatticeCount.finite_lattice_ball ((p - 1) / 2) r
  change C.ncard ≤ A.ncard
  refine Set.ncard_le_ncard_of_injOn (thetaCombination p K) ?_ ?_ hA
  · intro c hc
    exact thetaCombination_mem_augBall p K q hp2 hq2 x y hx hy h r c hc
  · intro c hc d hd hcd
    exact thetaCombination_injective p K hcd

end Catalan
