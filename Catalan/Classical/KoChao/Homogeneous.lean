module

public import Mathlib

/-!
# `Catalan.Classical.KoChao.Homogeneous`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
namespace Catalan.KoChao

lemma gcd_sub_homogeneous_sum
    (q : ℕ) (hq : q.Prime) (A B : ℤ) (hcop : IsCoprime A B) :
    Int.gcd (A - B) (∑ i ∈ Finset.range q, A ^ i * B ^ (q - 1 - i)) = 1 ∨
      Int.gcd (A - B) (∑ i ∈ Finset.range q, A ^ i * B ^ (q - 1 - i)) = q := by
  let S : ℤ := ∑ i ∈ Finset.range q, A ^ i * B ^ (q - 1 - i)
  have hcop_sub_B : IsCoprime (A - B) B := by
    rw [show A - B = A + (-1) * B by ring]
    exact (IsCoprime.add_mul_right_left_iff (x := A) (y := B) (z := -1)).2 hcop
  have hg_sub : (Int.gcd (A - B) S : ℤ) ∣ A - B :=
    Int.gcd_dvd_left (A - B) S
  have hg_sum : (Int.gcd (A - B) S : ℤ) ∣ S :=
    Int.gcd_dvd_right (A - B) S
  have hg_B : IsCoprime (Int.gcd (A - B) S : ℤ) B := by
    obtain ⟨u, v, huv⟩ := hcop_sub_B
    obtain ⟨t, ht⟩ := hg_sub
    refine ⟨u * t, v, ?_⟩
    calc
      (u * t) * (Int.gcd (A - B) S : ℤ) + v * B =
          u * ((Int.gcd (A - B) S : ℤ) * t) + v * B := by ring
      _ = u * (A - B) + v * B := by rw [← ht]
      _ = 1 := huv
  have hg_Bpow : IsCoprime (Int.gcd (A - B) S : ℤ) (B ^ (q - 1)) :=
    hg_B.pow_right
  have hg_qpow : (Int.gcd (A - B) S : ℤ) ∣
      (q : ℤ) * B ^ (q - 1) := by
    apply (dvd_geom_sum₂_iff_of_dvd_sub hg_sub).mp
    exact hg_sum
  have hg_q : (Int.gcd (A - B) S : ℤ) ∣ (q : ℤ) := by
    apply hg_Bpow.dvd_of_dvd_mul_left
    simpa only [mul_comm] using hg_qpow
  have hg_nat : Int.gcd (A - B) S ∣ q :=
    Int.natCast_dvd_natCast.mp hg_q
  have hcases := (Nat.dvd_prime hq).mp hg_nat
  simpa only [S] using hcases

end Catalan.KoChao
