module

public import Catalan.Density.UnramifiedPreservedPrime
public import Catalan.Density.NativeFrobenius
public import Catalan.Density.FrobeniusPower
public import Catalan.Density.FiniteT
public import Catalan.Density.AbsoluteT

/-!
# `Catalan.Density.DensityTheorem`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma exists_arithmeticFrob_nonzero_power
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime) (σ : L ≃ₐ[ℚ] L) (hne : σ ≠ 1) (hpow : σ ^ q = 1)
    (hcentral : ∀ τ : L ≃ₐ[ℚ] L, τ * σ = σ * τ → τ ^ q = 1)
    (S : Finset ℕ) :
    ∃ ell : ℕ, ell.Prime ∧ ell ∉ S ∧
      ∃ (P : Ideal (𝓞 L)) (a : ℕ), 0 < a ∧ a < q ∧ IsArithmeticFrob ell P (σ ^ a) := by
  obtain ⟨ell, hell, havoid, P, hmax, hbot, hmem, hunram, hpres⟩ :=
    exists_unramified_preserved_prime L q hq σ hne hpow S
  obtain ⟨ρ, hρ⟩ := exists_arithmeticFrob_at_unramified_prime L ell hell P hmax hbot hmem hunram
  obtain ⟨a, ha0, haq, ha⟩ := arithmeticFrob_nonzero_power_of_prime_centralizer
    L q hq σ hne hpow hcentral ell hell P hpres ρ hρ
  exact ⟨ell, hell, havoid, P, a, ha0, haq, ha⟩

end Catalan.A3
namespace Catalan

lemma densityInput (p q : ℕ) : DensityInput p q := by
  intro hadm σ hσ
  have instNumberFieldT : NumberField (A3.T p q) :=
    A3.numberField_T p q (hadm.hq.odd_of_ne_two hadm.hq2)
  have instGaloisT : IsGalois ℚ (A3.T p q) := A3.isGalois_T_rat p q hadm.hp.pos hadm.hq.pos
  obtain ⟨ell, hell, havoid, P, a, ha0, haq, ha⟩ :=
    A3.exists_arithmeticFrob_nonzero_power (A3.T p q) q hadm.hq σ hσ.ne_one hσ.pow_eq_one
      hσ.centralizer_exponent {p, q}
  have hne : ell ≠ p ∧ ell ≠ q := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using havoid
  exact ⟨ell, hell, hne.1, hne.2, P, a, ha0, haq, ha⟩

end Catalan
