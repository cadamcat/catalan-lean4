import Catalan.Stickelberger.MinusSmall
import Catalan.Stickelberger.MinusElement
import Catalan.Wieferich.Minus
import Catalan.Cassels.Elementary

set_option autoImplicit false
noncomputable section
open NumberField
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [hq : Fact q.Prime]

omit hq in
lemma q_smul_mem_mihIdeal (x : ℤ) (hp2 : p ≠ 2) (T : R p K) :
    (q : ℤ) • T ∈ mihIdeal p K q x hp2 := by
  refine ⟨upow p K (xmζ p K x hp2) T, ?_⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact (upowAddHom p K (xmζ p K x hp2)).map_nsmul q T

lemma θminus_mem_mihIdeal
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (k : ℕ) :
    θminus p K k ∈ mihIdeal p K q x hp2 := by
  have hpq : p ≠ q := by
    intro he
    subst q
    exact cassels_equal_exponents_false p hp.out hp2 x y hx hy h
  have hgen (j : ℕ) : ΘS p K j ∈ stickSpan p K :=
    Submodule.subset_span (Or.inl ⟨j, rfl⟩)
  change ∃ b : Kˣ, upow p K (xmζ p K x hp2) (θminus p K k) = b ^ q
  rw [θminus_eq_minusPart]
  exact A1e.minus_stick_qth p K q hq.out hp2 hq2 hpq x y hx hy h _
    ((stickSpan p K).sub_mem (hgen _) (hgen _))

lemma small_minus_mem_mihAug
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hsmall : p = 3 ∨ p = 5 ∨ p = 7)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1 : R p K) ∈
      mihAug p K q x hp2 := by
  let e : R p K := MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1
  let I := mihIdeal p K q x hp2
  have hθ (k : ℕ) : θminus p K k ∈ I :=
    θminus_mem_mihIdeal p K q hp2 hq2 x y hx hy h k
  have hhalve (h2 : (2 : ℤ) • e ∈ I) : e ∈ I := by
    have hq' : (q : ℤ) • e ∈ I := q_smul_mem_mihIdeal p K q x hp2 e
    obtain ⟨t, ht⟩ := hq.out.odd_of_ne_two hq2
    have hcast : (q : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
    have hcoef : ((t : ℤ) + 1) * 2 - (q : ℤ) = 1 := by omega
    have hm := I.sub_mem (I.toAddSubgroup.zsmul_mem h2 ((t : ℤ) + 1)) hq'
    rw [smul_smul, ← sub_smul, hcoef, one_smul] at hm
    exact hm
  have he : e ∈ I := by
    rcases hsmall with hp3 | hp5 | hp7
    · have hm := hθ 1
      rw [θminus_small_three p K hp3] at hm
      simpa only [neg_neg] using I.neg_mem hm
    · have hm := I.add_mem (hθ 1) (hθ 2)
      rw [θminus_small_five p K hp5] at hm
      apply hhalve
      simpa only [neg_smul, neg_neg] using I.neg_mem hm
    · have hm := I.add_mem (hθ 2) (hθ 3)
      rw [θminus_small_seven p K hp7] at hm
      apply hhalve
      simpa only [neg_smul, neg_neg] using I.neg_mem hm
  refine ⟨he, ?_⟩
  simp only [weight_sub, weight_single, sub_self]

lemma small_conductor_aug_witness
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hsmall : p = 3 ∨ p = 5 ∨ p = 7)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    ∃ T : R p K, T ∈ mihAug p K q x hp2 ∧ T ≠ 0 ∧ size p K T = 2 := by
  exact ⟨_, small_minus_mem_mihAug p K q hp2 hq2 hsmall x y hx hy h,
    minus_element_ne_zero p K hp2, minus_element_size p K hp2⟩

end Catalan
