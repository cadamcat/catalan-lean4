module

public import Mathlib

/-!
# `Catalan.Counting.Defs`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan

def S (n r : ℕ) : ℕ := Set.ncard {c : Fin n → ℤ | ∑ i, |c i| ≤ r}

namespace LatticeCount

def countPolynomial (n r : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), 2 ^ k * n.choose k * r.choose k

lemma finite_lattice_ball (n r : ℕ) :
    Set.Finite {c : Fin n → ℤ | ∑ i, |c i| ≤ r} := by
  classical
  let B := {m : ℤ // m ∈ Set.Icc (-(r : ℤ)) (r : ℤ)}
  let : Fintype B := (Set.finite_Icc (-(r : ℤ)) (r : ℤ)).fintype
  let C := {c : Fin n → ℤ // ∑ i, |c i| ≤ r}
  have hb (c : C) (i : Fin n) : |c.val i| ≤ (r : ℤ) := by
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (c.val j))
      (Finset.mem_univ i)).trans c.property
  let f : C → (Fin n → B) := fun c i => ⟨c.val i, abs_le.mp (hb c i)⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  change Finite C
  exact Finite.of_injective f hf

lemma S_zero_dim (r : ℕ) : S 0 r = 1 := by
  have he : {c : Fin 0 → ℤ | ∑ i, |c i| ≤ r} = {fun _ => (0 : ℤ)} := by
    ext c
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Nat.cast_nonneg r⟩
  simp only [S, he, Set.ncard_singleton]

end LatticeCount
end Catalan
