module

public import Catalan.Cassels.Elementary

/-!
# `Catalan.Cassels.Modular`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

/-- In the field with q elements, a p-th root of unity is trivial when
p is prime and larger than q. -/
lemma cassels_prime_root_mod (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (u : ℤ) (hup : (q : ℤ) ∣ u ^ p - 1) :
    (q : ℤ) ∣ u - 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hz : (u : ZMod q) ^ p = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_one] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ p - 1) q).mpr hup
  have hu0 : (u : ZMod q) ≠ 0 := by
    intro h0
    simp [h0, hp.ne_zero] at hz
  have hordp : orderOf (u : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hz
  have hordq : orderOf (u : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hu0
  have hord1 : orderOf (u : ZMod q) = 1 := by
    rcases (Nat.dvd_prime hp).mp hordp with h1 | heq
    · exact h1
    · rw [heq] at hordq
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hordq
      omega
  have hu1 : (u : ZMod q) = 1 := orderOf_eq_one_iff.mp hord1
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u - 1) q).mp
  simp only [Int.cast_sub, Int.cast_one, hu1, sub_self]

#print axioms cassels_prime_root_mod

end Catalan
