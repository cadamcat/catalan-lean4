module

public import Catalan.Stickelberger.SquareZeroSection
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# `Catalan.Stickelberger.SectionBridge`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- The kernel of the reduction `A ⧸ I ^ 2 → A ⧸ I` is square zero. -/
theorem quotient_factor_sq_ker {A : Type*} [CommRing A] (I : Ideal A)
    (z : A ⧸ I ^ 2)
    (hz : Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero : I ^ 2 ≤ I) z = 0) :
    z ^ 2 = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.Quotient.factor_mk] at hz
  have ha : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha 2)

/-- Upgrading a residue-field reduction of a multiplicative character to an
exact identity modulo `I ^ 2`: Teichmüller values are fixed by the residue
cardinality power, so the square-zero coefficient section recovers them. -/
theorem exists_residue_section_sq
    {F A : Type*} [Field F] [Fintype F] [CommRing A] (I : Ideal A) (ell : ℕ)
    [CharP F ell] [CharP (A ⧸ I ^ 2) ell]
    (f : A ⧸ I ^ 2 →+* F) (hf : Function.Surjective f)
    (hker : ∀ z : A ⧸ I ^ 2, f z = 0 → z ^ 2 = 0)
    (χ : MulChar F A)
    (hpow : ∀ x : F, (χ x) ^ Fintype.card F = χ x)
    (hredI : ∀ x : F, f (Ideal.Quotient.mk (I ^ 2) (χ x)) = x⁻¹) :
    ∃ ι : F →+* A ⧸ I ^ 2, ∀ x : F, Ideal.Quotient.mk (I ^ 2) (χ x) = ι x⁻¹ := by
  obtain ⟨ι, hι, -⟩ := exists_squareZero_residue_section ell f hf hker
  refine ⟨ι, fun x => ?_⟩
  have hz : (Ideal.Quotient.mk (I ^ 2) (χ x)) ^ Fintype.card F
      = Ideal.Quotient.mk (I ^ 2) (χ x) := by
    rw [← map_pow, hpow x]
  have hfix := residue_section_eq_of_pow_card_eq f ι hι hz
  rw [hredI x] at hfix
  exact hfix.symm

end Catalan.Stickelberger
