import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma isUnramifiedAtInfinitePlaces_of_odd_exponent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (q : ℕ) (hq : Odd q)
    (hpow : ∀ σ : L ≃ₐ[K] L, σ ^ q = 1) :
    IsUnramifiedAtInfinitePlaces K L := by
  apply IsUnramifiedAtInfinitePlaces_of_odd_card_aut
  apply Nat.not_even_iff_odd.mp
  intro hcard
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card'
    (G := L ≃ₐ[K] L) 2 hcard.two_dvd
  have hdvd : 2 ∣ q := hσ ▸ orderOf_dvd_of_pow_eq_one (hpow σ)
  exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hdvd)

end Catalan.A3
