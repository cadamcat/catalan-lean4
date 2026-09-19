import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.CharP.Frobenius

noncomputable section
namespace Catalan.Stickelberger

/-- A finite residue field has a coefficient-field section across a square-zero
kernel in equal characteristic. Raising any lift to the residue cardinality
constructs the section. -/
theorem exists_squareZero_residue_section {F B : Type*}
    [Field F] [Fintype F] [CommRing B] (p : ℕ) [CharP F p] [CharP B p]
    (f : B →+* F) (hf : Function.Surjective f)
    (hker : ∀ z : B, f z = 0 → z ^ 2 = 0) :
    ∃ ι : F →+* B,
      (∀ b : B, ι (f b) = b ^ Fintype.card F) ∧ f.comp ι = RingHom.id F := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  let : Fact p.Prime := ⟨hp⟩
  let Φ : B →+* B := iterateFrobenius B p n
  have hΦ (b : B) : Φ b = b ^ Fintype.card F := by
    change b ^ p ^ (n : ℕ) = _
    rw [← hcard]
  have hk : RingHom.ker f ≤ RingHom.ker Φ := by
    intro z hz
    apply RingHom.mem_ker.mpr
    rw [hΦ]
    exact pow_eq_zero_of_le Fintype.one_lt_card (hker z (RingHom.mem_ker.mp hz))
  let ι : F →+* B := f.liftOfSurjective hf ⟨Φ, hk⟩
  have hι (b : B) : ι (f b) = b ^ Fintype.card F := by
    change (f.liftOfSurjective hf) ⟨Φ, hk⟩ (f b) = _
    rw [RingHom.liftOfSurjective_comp_apply, hΦ]
  refine ⟨ι, hι, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := hf x
  change f (ι (f b)) = f b
  rw [hι, map_pow, FiniteField.pow_card]

/-- The section recovers any lift already fixed by the cardinality power. -/
lemma residue_section_eq_of_pow_card_eq {F B : Type*}
    [Field F] [Fintype F] [CommRing B]
    (f : B →+* F) (ι : F →+* B)
    (hι : ∀ b : B, ι (f b) = b ^ Fintype.card F)
    {z : B} (hz : z ^ Fintype.card F = z) : ι (f z) = z := by
  rw [hι, hz]

end Catalan.Stickelberger

