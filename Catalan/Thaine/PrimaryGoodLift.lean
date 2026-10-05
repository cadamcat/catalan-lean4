module

public import Catalan.Thaine.PrimaryNilpotence
public import Catalan.Thaine.FrobeniusPower

/-!
# `Catalan.Thaine.PrimaryGoodLift`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma exists_good_primary_power
    (R : Type*) [Ring R] (S : Type*) [CommRing S] [Finite S] [IsReduced S]
    (q : ℕ) [Fact q.Prime] [CharP S q] (red : R →+* S)
    (A : Type*) [AddCommGroup A] [Finite A] (rho : R →+* Module.End ℤ A)
    (Theta : R) (hTheta : ∀ a : A, ∃ b : A, rho Theta a = q • b) :
    ∃ n : ℕ, 0 < n ∧ red (Theta ^ n) = red Theta ∧
      ∀ a : A, (∃ k : ℕ, (q ^ k) • a = 0) → rho (Theta ^ n) a = 0 := by
  obtain ⟨N, hN⟩ := exists_primary_action_nilpotence A q (rho Theta) hTheta
  obtain ⟨m, hm, hfix⟩ := exists_large_frobenius_fixed_power S q (red Theta) N
  refine ⟨q ^ m, pow_pos (Fact.out : q.Prime).pos _, ?_, ?_⟩
  · simpa only [map_pow] using hfix
  · intro a ha
    rw [map_pow]
    exact hN (q ^ m) hm a ha

end Catalan.Thaine
