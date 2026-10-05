module

public import Mathlib

/-!
# `Catalan.CaseOne.SemisimpleIdeal`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Semisimple
variable (q : ℕ) [Fact q.Prime]
variable (G : Type*) [CommGroup G] [Finite G]

omit [CommGroup G] [Finite G] in
private lemma card_cast_ne_zero (hq : ¬ q ∣ Nat.card G) :
    (Nat.card G : ZMod q) ≠ 0 := by
  intro hz
  apply hq
  exact (ZMod.natCast_eq_zero_iff (Nat.card G) q).mp hz

lemma groupRing_ideal_mul_self (hq : ¬ q ∣ Nat.card G)
    (I : Ideal (MonoidAlgebra (ZMod q) G)) : I * I = I := by
  have hcard := card_cast_ne_zero q G hq
  have instCard : NeZero (Nat.card G : ZMod q) := ⟨hcard⟩
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  rw [hI, Ideal.span_singleton_mul_span_singleton, he.eq]

lemma groupRing_ideal_pow_eq_self (hq : ¬ q ∣ Nat.card G)
    (I : Ideal (MonoidAlgebra (ZMod q) G)) (n : ℕ) (hn : 0 < n) : I ^ n = I := by
  have hII := groupRing_ideal_mul_self q G hq I
  induction n with
  | zero => omega
  | succ n ih =>
      rw [pow_succ]
      cases n with
      | zero => simp
      | succ n =>
          rw [ih (by omega), hII]

lemma groupRing_ideal_mul_eq_inf (hq : ¬ q ∣ Nat.card G)
    (I J : Ideal (MonoidAlgebra (ZMod q) G)) : I * J = I ⊓ J := by
  have hcard := card_cast_ne_zero q G hq
  have instCard : NeZero (Nat.card G : ZMod q) := ⟨hcard⟩
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  obtain ⟨f, hf, hJ⟩ := IsSemisimpleRing.ideal_eq_span_idempotent J
  apply le_antisymm
  · exact Ideal.mul_le_inf
  · rw [hI, hJ, Ideal.span_singleton_mul_span_singleton]
    intro z hz
    rcases hz with ⟨hze, hzf⟩
    apply Ideal.mem_span_singleton.mpr
    have hze' : e * z = z := by
      rcases (Ideal.mem_span_singleton.mp hze) with ⟨a, ha⟩
      calc
        e * z = e * (e * a) := by rw [ha]
        _ = (e * e) * a := by rw [mul_assoc]
        _ = e * a := by rw [he.eq]
        _ = z := ha.symm
    have hzf' : f * z = z := by
      rcases (Ideal.mem_span_singleton.mp hzf) with ⟨a, ha⟩
      calc
        f * z = f * (f * a) := by rw [ha]
        _ = (f * f) * a := by rw [mul_assoc]
        _ = f * a := by rw [hf.eq]
        _ = z := ha.symm
    refine ⟨z, ?_⟩
    calc
      z = e * z := hze'.symm
      _ = e * (f * z) := by rw [hzf']
      _ = (e * f) * z := by ring

end Catalan.Semisimple
