import Mathlib

set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace Catalan.Primary

def primaryPolynomial (q : ℕ) : ℤ[X] :=
  Polynomial.ofFn q (fun i => if i.val = 0 then 0 else (q.choose i.val / q : ℕ))

lemma primaryPolynomial_natDegree_lt (q : ℕ) (hq : 0 < q) :
    (primaryPolynomial q).natDegree < q := by
  exact Polynomial.ofFn_natDegree_lt hq _

lemma primaryPolynomial_coeff_pred (q : ℕ) (hq : q.Prime) :
    (primaryPolynomial q).coeff (q - 1) = 1 := by
  unfold primaryPolynomial
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by have := hq.two_le; omega)]
  simp only [show q - 1 ≠ 0 by have := hq.two_le; omega, if_false]
  have hc : q.choose (q - 1) = q := by
    rw [Nat.choose_symm hq.one_le, Nat.choose_one_right]
  rw [hc, Nat.div_self hq.pos]
  norm_num

lemma primaryPolynomial_identity (q : ℕ) (hq : q.Prime) :
    C (q : ℤ) * primaryPolynomial q = (1 + X) ^ q - 1 - X ^ q := by
  ext n
  rw [coeff_C_mul, coeff_sub, coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
  by_cases hn0 : n = 0
  · subst n
    simp [primaryPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hq.pos, Ne.symm hq.ne_zero]
  by_cases hnq : n = q
  · subst n
    simp [primaryPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ le_rfl, hq.ne_zero]
  by_cases hn : n < q
  · rw [primaryPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
    simp only [hn0, if_false, hnq, sub_zero]
    exact_mod_cast (Nat.mul_div_cancel' (hq.dvd_choose_self hn0 hn))
  · have hqn : q < n := by omega
    simp [primaryPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hn),
      Nat.choose_eq_zero_of_lt hqn, hn0, hnq]

lemma primaryPolynomial_natDegree (q : ℕ) (hq : q.Prime) :
    (primaryPolynomial q).natDegree = q - 1 := by
  have hl := primaryPolynomial_natDegree_lt q hq.pos
  have hh : q - 1 ≤ (primaryPolynomial q).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [primaryPolynomial_coeff_pred q hq]; norm_num)
  omega

lemma primaryPolynomial_monic (q : ℕ) (hq : q.Prime) :
    (primaryPolynomial q).Monic := by
  change (primaryPolynomial q).coeff (primaryPolynomial q).natDegree = 1
  rw [primaryPolynomial_natDegree q hq, primaryPolynomial_coeff_pred q hq]

end Catalan.Primary
