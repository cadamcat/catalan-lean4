module

public import Catalan.Stickelberger.MinusSpanDefs

/-!
# `Catalan.Stickelberger.MinusSpanCore`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma theta_minus_spans_of_reflection (hp2 : p ≠ 2)
    (hreflect : ∀ k : ℕ, 1 ≤ k → k < p →
      minusLinearMap p K (ΘS p K k + ΘS p K (p - k)) =
        minusLinearMap p K (pθ p K)) :
    (stickSpan p K).map (minusLinearMap p K) = minusGeneratorSpan p K := by
  let n : ℕ := (p - 1) / 2
  let f := minusLinearMap p K
  let M := minusGeneratorSpan p K
  let D : ℕ → R p K := fun j => f (ΘS p K j)
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt
    (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2))
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2
  have hnpos : 1 ≤ n := by dsimp only [n]; omega
  have hpEq : p = 2 * n + 1 := by dsimp only [n]; omega
  have hD0 : D 0 = 0 := by simp only [D, ΘS_zero, map_zero]
  have hD1 : D 1 = 0 := by simp only [D, ΘS_one, map_zero]
  have hrec (j : ℕ) : D (j + 1) = D j + θminus p K j := by
    change f (ΘS p K (j + 1)) = f (ΘS p K j) +
      f (ΘS p K (j + 1) - ΘS p K j)
    rw [map_sub]
    abel
  have hθ (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) : θminus p K j ∈ M := by
    change θminus p K j ∈ Submodule.span ℤ
      (Set.range (fun i : Fin n => θminus p K (i.val + 1)))
    apply Submodule.subset_span
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    change θminus p K (j - 1 + 1) = θminus p K j
    rw [Nat.sub_add_cancel hj]
  have hsmall : ∀ j : ℕ, j ≤ n + 1 → D j ∈ M := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [hD0]
      exact M.zero_mem
    | succ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst j
        rw [hD1]
        exact M.zero_mem
      · rw [hrec]
        exact M.add_mem (ih (by omega)) (hθ j (by omega) (by omega))
  have hpθ : f (pθ p K) ∈ M := by
    have hcomp : p - n = n + 1 := by omega
    have he : D n + D (n + 1) = f (pθ p K) := by
      simpa only [D, hcomp, map_add] using hreflect n hnpos (by omega)
    rw [← he]
    exact M.add_mem (hsmall n (by omega)) (hsmall (n + 1) le_rfl)
  have hres (j : ℕ) (hjp : j < p) : D j ∈ M := by
    by_cases hj : j ≤ n + 1
    · exact hsmall j hj
    · have he : D j + D (p - j) = f (pθ p K) := by
        simpa only [D, map_add] using hreflect j (by omega) hjp
      have hsolve : D j = f (pθ p K) - D (p - j) := eq_sub_of_add_eq he
      rw [hsolve]
      exact M.sub_mem hpθ (hsmall (p - j) (by omega))
  have hall (j : ℕ) : D j ∈ M := by
    dsimp only [D]
    rw [ΘS_mod_decomposition, map_add, map_smul]
    exact M.add_mem (M.smul_mem ((j / p : ℕ) : ℤ) hpθ)
      (hres (j % p) (Nat.mod_lt j (Fact.out : p.Prime).pos))
  have hgen (j : ℕ) : ΘS p K j ∈ stickSpan p K :=
    Submodule.subset_span (Or.inl ⟨j, rfl⟩)
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    intro A hA
    change f A ∈ M
    rcases hA with ⟨j, rfl⟩ | hA
    · exact hall j
    · have he : A = pθ p K := Set.mem_singleton_iff.mp hA
      rw [he]
      exact hpθ
  · change Submodule.span ℤ (Set.range (fun i : Fin n => θminus p K (i.val + 1))) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨ΘS p K (i.val + 1 + 1) - ΘS p K (i.val + 1),
      (stickSpan p K).sub_mem (hgen _) (hgen _), ?_⟩
    rfl

end Catalan
