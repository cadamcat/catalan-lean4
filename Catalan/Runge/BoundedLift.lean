module

public import Catalan.Runge.Reduction
public import Catalan.CaseOne.GaloisRing

/-!
# `Catalan.Runge.BoundedLift`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance boundedLiftGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma exists_bounded_even_lift (q : ℕ) (hq : q.Prime) (Theta : R p K)
    (he : ∀ g : G p K,
      (Theta.coeff (ι p K * g) : ZMod q) = (Theta.coeff g : ZMod q))
    (hw : (weight p K Theta : ZMod q) = 0) (hne : reduceFull p K q Theta ≠ 0) :
    ∃ (Psi : R p K) (m : ℕ),
      (∀ g, 0 ≤ Psi.coeff g) ∧ EvenCoefficients p K Psi ∧
      0 < m ∧ 2 * m ≤ p - 1 ∧ weight p K Psi = (m * q : ℕ) ∧
      reduceFull p K q Psi ≠ 0 ∧
      (reduceFull p K q Psi = reduceFull p K q Theta ∨
        reduceFull p K q Psi = -reduceFull p K q Theta) := by
  classical
  have instNeZeroQ : NeZero q := ⟨hq.ne_zero⟩
  let make (t : G p K → ℕ) : R p K := MonoidAlgebra.ofCoeff
    (Finsupp.onFinset Finset.univ (fun g => (t g : ℤ)) (fun _ _ => Finset.mem_univ _))
  have hcoeff (t : G p K → ℕ) (g : G p K) : (make t).coeff g = (t g : ℤ) := rfl
  have hweight (t : G p K → ℕ) : weight p K (make t) = ((∑ g, t g : ℕ) : ℤ) := by
    rw [weight_eq_sum]
    simp only [hcoeff, Nat.cast_sum]
  let n : G p K → ℕ := fun g => (Theta.coeff g : ZMod q).val
  let n' : G p K → ℕ := fun g => q - n g
  let N : ℕ := ∑ g : G p K, n g
  let N' : ℕ := ∑ g : G p K, n' g
  have hlt (g : G p K) : n g < q := ZMod.val_lt (Theta.coeff g : ZMod q)
  have hncast (g : G p K) : (n g : ZMod q) = (Theta.coeff g : ZMod q) :=
    ZMod.natCast_zmod_val _
  have hn'cast (g : G p K) : (n' g : ZMod q) = -(Theta.coeff g : ZMod q) := by
    simp only [n', Nat.cast_sub (hlt g).le, ZMod.natCast_self, zero_sub, hncast]
  have he0 (g : G p K) : n (ι p K * g) = n g := congrArg ZMod.val (he g)
  have he1 (g : G p K) : n' (ι p K * g) = n' g := by
    dsimp only [n']
    rw [he0]
  have hred0 : reduceFull p K q (make n) = reduceFull p K q Theta := by
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro g
    simp only [reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom,
      hcoeff, Int.cast_natCast]
    exact hncast g
  have hred1 : reduceFull p K q (make n') = -reduceFull p K q Theta := by
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro g
    simp only [reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom,
      hcoeff, Int.cast_natCast, MonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    exact hn'cast g
  have hw0 : (N : ZMod q) = 0 := by
    have heq : (N : ZMod q) = (weight p K Theta : ZMod q) := by
      simp only [N, Nat.cast_sum, weight_eq_sum, Int.cast_sum]
      apply Finset.sum_congr rfl
      intro g hg
      exact hncast g
    exact heq.trans hw
  have hd0 : q ∣ N := (ZMod.natCast_eq_zero_iff N q).mp hw0
  have hcard : Fintype.card (G p K) = p - 1 := by
    rw [← Nat.card_eq_fintype_card, UnitModule.cyclotomicGal_card p K]
  have htotal : N + N' = q * (p - 1) := by
    change (∑ g : G p K, n g) + (∑ g : G p K, (q - n g)) = _
    rw [← Finset.sum_add_distrib]
    have heq (g : G p K) : n g + (q - n g) = q := Nat.add_sub_of_le (hlt g).le
    simp only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    exact Nat.mul_comm _ _
  have hd1 : q ∣ N' := by
    have hsum : q ∣ N + N' := by rw [htotal]; exact dvd_mul_right q (p - 1)
    exact (Nat.dvd_add_right hd0).mp hsum
  obtain ⟨t, hte, htd, hsmall, htr, hsign⟩ :
      ∃ t : G p K → ℕ, (∀ g, t (ι p K * g) = t g) ∧
        q ∣ (∑ g, t g) ∧ 2 * (∑ g, t g) ≤ q * (p - 1) ∧
        reduceFull p K q (make t) ≠ 0 ∧
        (reduceFull p K q (make t) = reduceFull p K q Theta ∨
          reduceFull p K q (make t) = -reduceFull p K q Theta) := by
    by_cases hs : N ≤ N'
    · refine ⟨n, he0, hd0, ?_, ?_, Or.inl hred0⟩
      · change 2 * N ≤ q * (p - 1)
        omega
      · rwa [hred0]
    · refine ⟨n', he1, hd1, ?_, ?_, Or.inr hred1⟩
      · change 2 * N' ≤ q * (p - 1)
        omega
      · rw [hred1]
        exact neg_ne_zero.mpr hne
  have htpos : 0 < ∑ g : G p K, t g := by
    by_contra ht
    have hzsum : (∑ g : G p K, t g) = 0 := Nat.eq_zero_of_not_pos ht
    have hzero (g : G p K) : t g = 0 := by
      have hle : t g ≤ ∑ j : G p K, t j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      omega
    have hmzero : make t = 0 := by
      apply MonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro g
      simp only [hcoeff, hzero, Nat.cast_zero, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    apply htr
    rw [hmzero, map_zero]
  obtain ⟨m, hmul⟩ := htd
  have hmpos : 0 < m := by
    rw [hmul] at htpos
    exact Nat.pos_of_mul_pos_left htpos
  have hmbound : 2 * m ≤ p - 1 := by
    have hmulbound : q * (2 * m) ≤ q * (p - 1) := by
      calc
        q * (2 * m) = 2 * (q * m) := by ring
        _ = 2 * (∑ g : G p K, t g) := by rw [hmul]
        _ ≤ q * (p - 1) := hsmall
    exact Nat.le_of_mul_le_mul_left hmulbound hq.pos
  refine ⟨make t, m, ?_, ?_, hmpos, hmbound, ?_, htr, hsign⟩
  · intro g
    rw [hcoeff]
    exact Int.natCast_nonneg _
  · intro g
    rw [hcoeff, hcoeff, hte]
  · rw [hweight, hmul, Nat.mul_comm q m]

end Catalan.Runge
