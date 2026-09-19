import Catalan.Counting.Defs

open scoped BigOperators
namespace Catalan.LatticeCount

private abbrev Ball (n r : ℕ) := {c : Fin n → ℤ // ∑ i, |c i| ≤ (r : ℤ)}

private noncomputable instance ballFintype (n r : ℕ) : Fintype (Ball n r) :=
  (finite_lattice_ball n r).fintype

lemma S_succ_dim (n r : ℕ) :
    S (n + 1) r = S n r + 2 * ∑ t ∈ Finset.range r, S n t := by
  classical
  have hpos (t : Fin r) : (0 : ℤ) < (r : ℤ) - (t.val : ℤ) := by
    have ht : (t.val : ℤ) < (r : ℤ) := by exact_mod_cast t.isLt
    omega
  let T := Ball n r ⊕ (Bool × (Σ t : Fin r, Ball n t.val))
  let f : T → Ball (n + 1) r := fun c => match c with
    | .inl b => ⟨Fin.cons 0 b.val, by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, abs_zero, zero_add]
          using b.property⟩
    | .inr (sign, ⟨t, b⟩) =>
        ⟨Fin.cons (if sign then (r : ℤ) - (t.val : ℤ) else -((r : ℤ) - (t.val : ℤ))) b.val, by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have ht := b.property
          have hp := hpos t
          cases sign <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg,
            abs_of_nonneg hp.le] <;> omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    rcases a with a | ⟨sa, ta, a⟩ <;> rcases b with b | ⟨sb, tb, b⟩
    · congr 1
      apply Subtype.ext
      funext i
      have hh := congrArg (fun c : Ball (n + 1) r => c.val i.succ) hab
      simpa only [f, Fin.cons_succ] using hh
    · have hh := congrArg (fun c : Ball (n + 1) r => c.val 0) hab
      have hp := hpos tb
      cases sb <;> simp only [f, Fin.cons_zero, Bool.false_eq_true, ite_false, ite_true] at hh <;> omega
    · have hh := congrArg (fun c : Ball (n + 1) r => c.val 0) hab
      have hp := hpos ta
      cases sa <;> simp only [f, Fin.cons_zero, Bool.false_eq_true, ite_false, ite_true] at hh <;> omega
    · have hh := congrArg (fun c : Ball (n + 1) r => c.val 0) hab
      change (if sa then (r : ℤ) - (ta.val : ℤ) else -((r : ℤ) - (ta.val : ℤ))) =
        (if sb then (r : ℤ) - (tb.val : ℤ) else -((r : ℤ) - (tb.val : ℤ))) at hh
      have hpa := hpos ta
      have hpb := hpos tb
      have hs : sa = sb := by
        cases sa <;> cases sb <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hh ⊢ <;> omega
      subst sb
      have htval : ta.val = tb.val := by
        cases sa <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hh <;> omega
      have ht : ta = tb := Fin.ext htval
      subst tb
      have htail : a = b := by
        apply Subtype.ext
        funext i
        have hh := congrArg (fun c : Ball (n + 1) r => c.val i.succ) hab
        simpa only [f, Fin.cons_succ] using hh
      subst b
      rfl
  have hsurj : Function.Surjective f := by
    intro c
    have hc : |c.val 0| + ∑ i : Fin n, |c.val i.succ| ≤ (r : ℤ) := by
      simpa only [Fin.sum_univ_succ] using c.property
    have htail0 : (0 : ℤ) ≤ ∑ i : Fin n, |c.val i.succ| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    by_cases hc0 : c.val 0 = 0
    · have htail : ∑ i : Fin n, |Fin.tail c.val i| ≤ (r : ℤ) := by
        simpa only [Fin.tail, hc0, abs_zero, zero_add] using hc
      refine ⟨Sum.inl ⟨Fin.tail c.val, htail⟩, ?_⟩
      apply Subtype.ext
      change Fin.cons 0 (Fin.tail c.val) = c.val
      rw [← hc0]
      exact Fin.cons_self_tail _
    · have hm : (c.val 0).natAbs ≤ r := by
        have he : ((c.val 0).natAbs : ℤ) ≤ (r : ℤ) := by
          rw [Int.natCast_natAbs]
          omega
        exact_mod_cast he
      have hmpos : 0 < (c.val 0).natAbs := Int.natAbs_pos.mpr hc0
      let t : Fin r := ⟨r - (c.val 0).natAbs, by omega⟩
      have ht : (r : ℤ) - (t.val : ℤ) = |c.val 0| := by
        dsimp only [t]
        rw [Nat.cast_sub hm, Int.natCast_natAbs]
        ring
      have htail : ∑ i : Fin n, |Fin.tail c.val i| ≤ (t.val : ℤ) := by
        change (∑ i : Fin n, |c.val i.succ|) ≤ (t.val : ℤ)
        omega
      by_cases hcp : 0 < c.val 0
      · refine ⟨Sum.inr (true, ⟨t, ⟨Fin.tail c.val, htail⟩⟩), ?_⟩
        apply Subtype.ext
        change Fin.cons ((r : ℤ) - (t.val : ℤ)) (Fin.tail c.val) = c.val
        rw [ht, abs_of_pos hcp]
        exact Fin.cons_self_tail _
      · have hcn : c.val 0 < 0 := by omega
        refine ⟨Sum.inr (false, ⟨t, ⟨Fin.tail c.val, htail⟩⟩), ?_⟩
        apply Subtype.ext
        change Fin.cons (-((r : ℤ) - (t.val : ℤ))) (Fin.tail c.val) = c.val
        rw [ht, abs_of_neg hcn, neg_neg]
        exact Fin.cons_self_tail _
  have hcard (n r : ℕ) : Fintype.card (Ball n r) = S n r :=
    @Set.fintypeCard_eq_ncard (Fin n → ℤ)
      {c | ∑ i, |c i| ≤ (r : ℤ)} (ballFintype n r)
  calc
    S (n + 1) r = Fintype.card (Ball (n + 1) r) := (hcard _ _).symm
    _ = Fintype.card T := (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = S n r + 2 * ∑ t ∈ Finset.range r, S n t := by
      simp only [T, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_sigma, hcard]
      rw [Fin.sum_univ_eq_sum_range]

end Catalan.LatticeCount
