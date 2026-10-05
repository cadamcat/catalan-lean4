module

public import Mathlib

/-!
# `Catalan.Classical.Lebesgue.Orders`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Lebesgue

lemma lebesgue_even_term_order
    (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : 2 ≤ j) (hjp : 2 * j ≤ p)
    (v : ℤ) (hv : Even v) (hv0 : v ≠ 0) :
    emultiplicity (2 : ℤ) ((p.choose 2 : ℤ) * v ^ 2) <
      emultiplicity (2 : ℤ) ((p.choose (2 * j) : ℤ) * v ^ (2 * j)) := by
  let twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  have hj0 : j ≠ 0 := by omega
  have hjodd0 : 2 * j - 1 ≠ 0 := by omega
  have hchoose0 : p.choose 2 ≠ 0 := Nat.choose_ne_zero (le_trans (by decide : 2 ≤ 3) hp3)
  have hchoosej0 : p.choose (2 * j) ≠ 0 := Nat.choose_ne_zero hjp
  have hchooseTail0 : (p - 2).choose (2 * j - 2) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hchoose2 : (2 * j).choose 2 = j * (2 * j - 1) := by
    rw [Nat.choose_two_right]
    calc
      2 * j * (2 * j - 1) / 2 = (j * (2 * j - 1) * 2) / 2 := by congr 1; ring
      _ = j * (2 * j - 1) := Nat.mul_div_cancel _ (by decide)
  have hbin : p.choose (2 * j) * (j * (2 * j - 1)) =
      p.choose 2 * (p - 2).choose (2 * j - 2) := by
    simpa only [hchoose2] using (Nat.choose_mul (n := p) (k := 2 * j) (s := 2) (by omega))
  have hodd : padicValNat 2 (2 * j - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  have horder : padicValNat 2 (p.choose (2 * j)) + padicValNat 2 j =
      padicValNat 2 (p.choose 2) + padicValNat 2 ((p - 2).choose (2 * j - 2)) := by
    have hh := congrArg (padicValNat 2) hbin
    rw [padicValNat.mul hchoosej0 (mul_ne_zero hj0 hjodd0),
      padicValNat.mul hj0 hjodd0, hodd, add_zero,
      padicValNat.mul hchoose0 hchooseTail0] at hh
    exact hh
  have hjorder : padicValNat 2 j < 2 * j - 2 :=
    ((padicValNat_le_nat_log j).trans_lt (Nat.log_lt_self 2 hj0)).trans_le (by omega)
  have hvabs0 : v.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hv0
  have hvorder : 1 ≤ padicValNat 2 v.natAbs :=
    one_le_padicValNat_of_dvd hvabs0 (even_iff_two_dvd.mp hv.natAbs)
  have hmain : padicValNat 2 (p.choose 2 * v.natAbs ^ 2) <
      padicValNat 2 (p.choose (2 * j) * v.natAbs ^ (2 * j)) := by
    rw [padicValNat.mul hchoose0 (pow_ne_zero _ hvabs0),
      padicValNat.mul hchoosej0 (pow_ne_zero _ hvabs0),
      padicValNat.pow, padicValNat.pow]
    have hjadd : (2 * j - 2) + 2 = 2 * j := by omega
    have hmul : 2 * j - 2 ≤ (2 * j - 2) * padicValNat 2 v.natAbs := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * j - 2) hvorder
    have hdist : (2 * j - 2) * padicValNat 2 v.natAbs +
        2 * padicValNat 2 v.natAbs = 2 * j * padicValNat 2 v.natAbs := by
      rw [← Nat.add_mul, hjadd]
    omega
  have hA := Int.emultiplicity_natAbs 2 ((p.choose 2 : ℤ) * v ^ 2)
  have hB := Int.emultiplicity_natAbs 2 ((p.choose (2 * j) : ℤ) * v ^ (2 * j))
  norm_num only [Nat.cast_ofNat] at hA hB
  rw [← hA, ← hB]
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
  rw [← padicValNat_eq_emultiplicity (mul_ne_zero hchoose0 (pow_ne_zero _ hvabs0)),
    ← padicValNat_eq_emultiplicity (mul_ne_zero hchoosej0 (pow_ne_zero _ hvabs0))]
  exact_mod_cast hmain

lemma int_sum_ne_zero_of_unique_min_order
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∈ s)
    (f : ι → ℤ) (hfi : f i ≠ 0)
    (hmin : ∀ j ∈ s, j ≠ i →
      emultiplicity (2 : ℤ) (f i) < emultiplicity (2 : ℤ) (f j)) :
    ∑ j ∈ s, f j ≠ 0 := by
  let twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : emultiplicity (2 : ℤ) (f i) < ⊤ :=
    emultiplicity_lt_top.mpr (padicValRat.finite_int_prime_iff.mpr hfi)
  have hsum : ∀ t : Finset ι,
      (∀ j ∈ t, emultiplicity (2 : ℤ) (f i) < emultiplicity (2 : ℤ) (f j)) →
        emultiplicity (2 : ℤ) (f i) < emultiplicity (2 : ℤ) (∑ j ∈ t, f j) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.sum_empty, emultiplicity_zero] using hfin
    | @insert j t hjt ih =>
      intro ht
      rw [Finset.sum_insert hjt]
      apply lt_of_lt_of_le _ min_le_emultiplicity_add
      apply lt_min
      · exact ht j (Finset.mem_insert_self _ _)
      · exact ih (fun k hk => ht k (Finset.mem_insert_of_mem hk))
  have htail := hsum (s.erase i) (fun j hj =>
    hmin j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
  have heq : emultiplicity (2 : ℤ) (∑ j ∈ s, f j) = emultiplicity (2 : ℤ) (f i) := by
    rw [← Finset.sum_erase_add _ _ hi]
    exact emultiplicity_add_of_gt htail
  intro hz
  rw [hz, emultiplicity_zero] at heq
  exact (ne_of_lt hfin) heq.symm

end Catalan.Lebesgue

