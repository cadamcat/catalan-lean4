module

public import Catalan.Classical.Lebesgue.Binomial
public import Catalan.Classical.Lebesgue.Orders

/-!
# `Catalan.Classical.Lebesgue.RealPart`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Lebesgue
open scoped BigOperators

lemma gaussian_even_imag_real_ne_one
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (v : ℤ) (hv : Even v) (hv0 : v ≠ 0) :
    ((⟨1, v⟩ : GaussianInt) ^ p).re ≠ 1 := by
  classical
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  let f : ℕ → ℤ := fun j => (-1 : ℤ) ^ j * (p.choose (2 * j) : ℤ) * v ^ (2 * j)
  let s := (Finset.range (p / 2 + 1)).erase 0
  have h1s : 1 ∈ s := by
    simp only [s, Finset.mem_erase, Finset.mem_range]
    omega
  have hf1 : f 1 ≠ 0 := by
    change (-1 : ℤ) ^ 1 * (p.choose (2 * 1) : ℤ) * v ^ (2 * 1) ≠ 0
    norm_num only [pow_one, mul_one, neg_one_mul]
    exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hp.two_le)))
      (pow_ne_zero 2 hv0)
  have h2prime : Prime (2 : ℤ) := by norm_num
  have horder (j : ℕ) : emultiplicity (2 : ℤ) (f j) =
      emultiplicity (2 : ℤ) ((p.choose (2 * j) : ℤ) * v ^ (2 * j)) := by
    dsimp only [f]
    rw [mul_assoc, emultiplicity_mul h2prime,
      emultiplicity_of_isUnit_right h2prime.not_isUnit (isUnit_one.neg.pow j), zero_add]
  have hmin : ∀ j ∈ s, j ≠ 1 → emultiplicity (2 : ℤ) (f 1) < emultiplicity (2 : ℤ) (f j) := by
    intro j hj hj1
    have hj' := Finset.mem_erase.mp hj
    have hjlt := Finset.mem_range.mp hj'.2
    have hj2 : 2 ≤ j := by omega
    have hjp : 2 * j ≤ p := by omega
    rw [horder 1, horder j]
    simpa only [mul_one] using lebesgue_even_term_order p j hp hp2 hj2 hjp v hv hv0
  have hnonzero := int_sum_ne_zero_of_unique_min_order s 1 h1s f hf1 hmin
  intro heq
  have hsum : (∑ j ∈ Finset.range (p / 2 + 1), f j) = 1 :=
    (gaussian_re_binomial v p).symm.trans heq
  have hsplit := Finset.sum_erase_add (s := Finset.range (p / 2 + 1)) (f := f)
    (show 0 ∈ Finset.range (p / 2 + 1) by simp)
  have hf0 : f 0 = 1 := by simp [f]
  change (∑ j ∈ s, f j) + f 0 = _ at hsplit
  rw [hf0, hsum] at hsplit
  exact hnonzero (by omega)

end Catalan.Lebesgue
