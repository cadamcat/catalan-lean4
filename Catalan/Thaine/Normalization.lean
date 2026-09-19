import Catalan.Thaine.MixedEpsilonUnit

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

def normalizedHalf (p : ℕ) (a : (ZMod p)ˣ) : ℕ :=
  (((1 - (a : ZMod p)) * (2 : ZMod p)⁻¹) : ZMod p).val

lemma normalizedHalf_congruence (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : (ZMod p)ˣ) :
    (p : ℤ) ∣ 2 * (normalizedHalf p a : ℤ) + ((a : ZMod p).val : ℤ) - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp2 h
  push_cast
  simp only [normalizedHalf, ZMod.natCast_zmod_val]
  field_simp [htwo]
  ring

lemma normalizedHalf_root {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ)
    (z : K) (hz : IsPrimitiveRoot z p) :
    z ^ (2 * (normalizedHalf p a : ℤ) + ((a : ZMod p).val : ℤ) - 1) = 1 :=
  (hz.zpow_eq_one_iff_dvd _).mpr (normalizedHalf_congruence p hp2 a)

def normalizedEpsilon {K : Type*} [Field K]
    (p : ℕ) (a : (ZMod p)ˣ) (z w : K) : K :=
  z ^ normalizedHalf p a * (z ^ (a : ZMod p).val - w) / (z - w)

def normalizedCircularValue {K : Type*} [Field K]
    (p : ℕ) (a : (ZMod p)ˣ) (z : K) : K := normalizedEpsilon p a z 1

lemma normalizedCircularValue_eq {K : Type*} [Field K]
    (p : ℕ) (a : (ZMod p)ˣ) (z : K) :
    normalizedCircularValue p a z =
      z ^ normalizedHalf p a * (1 - z ^ (a : ZMod p).val) / (1 - z) := by
  unfold normalizedCircularValue normalizedEpsilon
  rw [← neg_sub 1 (z ^ (a : ZMod p).val), ← neg_sub 1 z,
    mul_neg, neg_div_neg_eq]

lemma exists_normalized_epsilon_unit
    (K : Type*) [Field K] [NumberField K]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell)
    (a : (ZMod p)ˣ) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      ((u : NumberField.RingOfIntegers K) : K) = normalizedEpsilon p a z w := by
  simpa only [normalizedEpsilon, zpow_natCast] using
    exists_mixed_epsilon_unit K p ell hpe z w hz hw a (normalizedHalf p a : ℤ)

end Catalan.Thaine
