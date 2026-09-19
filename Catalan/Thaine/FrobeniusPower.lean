import Mathlib.FieldTheory.Perfect
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma exists_large_frobenius_fixed_power
    (R : Type*) [CommRing R] [Finite R] [IsReduced R]
    (q : ℕ) [Fact q.Prime] [CharP R q] (x : R) (B : ℕ) :
    ∃ m : ℕ, B ≤ q ^ m ∧ x ^ (q ^ m) = x := by
  have instExpChar : ExpChar R q := by infer_instance
  have instPerfectRing : PerfectRing R q := PerfectRing.ofFiniteOfIsReduced q R
  have hperiodic : x ∈ Function.periodicPts (frobenius R q) :=
    Function.Injective.mem_periodicPts (PerfectRing.bijective_frobenius.1) x
  obtain ⟨r, hr, hfix⟩ := Function.mem_periodicPts.mp hperiodic
  let m : ℕ := r * B
  have hqge : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hpow_bound : ∀ n : ℕ, n + 1 ≤ q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 2 ≤ 2 * (n + 1) := by omega
          _ ≤ q * (n + 1) := Nat.mul_le_mul_right (n + 1) hqge
          _ ≤ q * q ^ n := Nat.mul_le_mul_left q ih
          _ = q ^ n * q := Nat.mul_comm _ _
          _ = q ^ (n + 1) := by rw [pow_succ]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hB_le_m : B ≤ m := by
    dsimp [m]
    calc
      B = 1 * B := by simp
      _ ≤ r * B := Nat.mul_le_mul_right B hr1
  have hB_le_qm : B ≤ q ^ m := by
    exact hB_le_m.trans (Nat.le_succ m |>.trans (hpow_bound m))
  have hfix_m : Function.IsPeriodicPt (frobenius R q) m x := by
    dsimp [m]
    exact hfix.mul_const B
  have hpow : x ^ (q ^ m) = x := by
    have hiterate : ((frobenius R q)^[m]) x = x := hfix_m
    simpa only [iterate_frobenius] using hiterate
  exact ⟨m, hB_le_qm, hpow⟩

end Catalan.Thaine
