module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Fintype.Lattice

/-!
# `Catalan.Thaine.PrimaryNilpotence`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma exists_uniform_primary_exponent
    (A : Type*) [AddCommGroup A] [Finite A] (q : ℕ) :
    ∃ E : ℕ, ∀ a : A, (∃ k : ℕ, (q ^ k) • a = 0) → (q ^ E) • a = 0 := by
  classical
  let e : A → ℕ := fun a => if h : ∃ k : ℕ, (q ^ k) • a = 0 then h.choose else 0
  obtain ⟨a0, hmax⟩ := Finite.exists_max e
  refine ⟨e a0, ?_⟩
  intro a ha
  have hea : (q ^ e a) • a = 0 := by
    dsimp only [e]
    rw [dif_pos ha]
    exact ha.choose_spec
  rw [← Nat.sub_add_cancel (hmax a), pow_add, mul_smul, hea, smul_zero]

lemma exists_primary_action_nilpotence
    (A : Type*) [AddCommGroup A] [Finite A] (q : ℕ)
    (f : A →ₗ[ℤ] A) (hf : ∀ a : A, ∃ b : A, f a = q • b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : A, (∃ k : ℕ, (q ^ k) • a = 0) → (f ^ n) a = 0 := by
  have hiter : ∀ n : ℕ, ∀ a : A, ∃ b : A, (f ^ n) a = (q ^ n) • b := by
    intro n
    induction n with
    | zero =>
      intro a
      exact ⟨a, by simp⟩
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨c, hc⟩ := hf b
      refine ⟨c, ?_⟩
      rw [Module.End.iterate_succ', LinearMap.comp_apply, hb, map_nsmul, hc,
        ← mul_smul, ← pow_succ]
  obtain ⟨E, hE⟩ := exists_uniform_primary_exponent A q
  refine ⟨E, ?_⟩
  intro n hn a ha
  obtain ⟨b, hb⟩ := hiter n a
  have hprimary : ∃ k : ℕ, (q ^ k) • b = 0 := by
    obtain ⟨k, hk⟩ := ha
    refine ⟨k + n, ?_⟩
    rw [pow_add, mul_smul, ← hb, ← map_nsmul, hk, map_zero]
  have hEb := hE b hprimary
  rw [hb, ← Nat.sub_add_cancel hn, pow_add, mul_smul, hEb, smul_zero]

end Catalan.Thaine
