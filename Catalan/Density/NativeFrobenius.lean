import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma exists_arithmeticFrob_at_unramified_prime
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 L))
    (hPmax : P.IsMaximal) (hPbot : P ≠ ⊥) (hmem : (ell : 𝓞 L) ∈ P)
    (hunram : InertiaTrivial ℚ L P) :
    ∃ ρ : L ≃ₐ[ℚ] L, IsArithmeticFrob ell P ρ := by
  let instMaximalP : P.IsMaximal := hPmax
  let instPrimeEll : Fact ell.Prime := ⟨hell⟩
  let instFiniteQuotient : Finite (𝓞 L ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hPbot
  have hunder : P.under ℤ = Ideal.span {(ell : ℤ)} := by
    symm
    apply Ideal.IsMaximal.eq_of_le inferInstance
      (inferInstance : (P.under ℤ).IsPrime).ne_top
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    change algebraMap ℤ (𝓞 L) (ell : ℤ) ∈ P
    simpa using hmem
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = ell := by
    rw [hunder, Int.card_ideal_quot]
  let instInvariant : Algebra.IsInvariant ℤ (𝓞 L) (L ≃ₐ[ℚ] L) := inferInstance
  obtain ⟨ρ, hρ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (L ≃ₐ[ℚ] L) P
  refine ⟨ρ, hPmax, hPbot, hmem, instFiniteQuotient, hunram, ?_, ?_⟩
  · intro x
    change x ∈ P.comap (MulSemiringAction.toAlgHom ℤ (𝓞 L) ρ) ↔ x ∈ P
    rw [hρ.comap_eq]
  · intro x
    change ρ • x - x ^ ell ∈ P
    simpa only [hcard, MulSemiringAction.toAlgHom_apply] using hρ x

end Catalan.A3
