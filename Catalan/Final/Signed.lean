import Catalan.Final.Assembly

set_option autoImplicit false
namespace Catalan

theorem catalan_int_signed (x y : ℤ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p - y ^ q = 1) :
    p = 2 ∧ q = 3 ∧ (x = 3 ∨ x = -3) ∧ y = 2 :=
  by
    have hadd : x ^ p = y ^ q + 1 := by omega
    have hxpow_ne : x ^ p ≠ 0 := pow_ne_zero p hx
    have hypow_ne : y ^ q ≠ 0 := pow_ne_zero q hy
    have hxabs_pos : 0 < x.natAbs := by
      apply Nat.pos_of_ne_zero
      intro hxabs_zero
      exact hx (Int.natAbs_eq_zero.mp hxabs_zero)
    have hyabs_pos : 0 < y.natAbs := by
      apply Nat.pos_of_ne_zero
      intro hyabs_zero
      exact hy (Int.natAbs_eq_zero.mp hyabs_zero)
    by_cases hyq_pos : 0 < y ^ q
    · have hxp_pos : 0 < x ^ p := by omega
      have hxcast : ((x.natAbs ^ p : ℕ) : ℤ) = x ^ p := by
        rw [← Int.natAbs_pow]
        exact Int.natAbs_of_nonneg (le_of_lt hxp_pos)
      have hycast : ((y.natAbs ^ q : ℕ) : ℤ) = y ^ q := by
        rw [← Int.natAbs_pow]
        exact Int.natAbs_of_nonneg (le_of_lt hyq_pos)
      have hcast_add :
          ((x.natAbs ^ p : ℕ) : ℤ) = ((y.natAbs ^ q : ℕ) : ℤ) + 1 := by
        rw [hxcast, hycast]
        omega
      have hnat_add : x.natAbs ^ p = y.natAbs ^ q + 1 := by
        exact_mod_cast hcast_add
      have hnat_sub : x.natAbs ^ p - y.natAbs ^ q = 1 := by omega
      have hcat := Catalan.catalans_conjecture p q x.natAbs y.natAbs
        (by omega) (by omega) hxabs_pos hyabs_pos hnat_sub
      rcases hcat with ⟨hp2, hq3, hx3, hy2⟩
      have hx_class : x = 3 ∨ x = -3 := by
        simpa using (Int.natAbs_eq_iff.mp hx3)
      have hy_class : y = 2 ∨ y = -2 := by
        simpa using (Int.natAbs_eq_iff.mp hy2)
      have hy_eq : y = 2 := by
        rcases hy_class with hy_eq | hy_neg
        · exact hy_eq
        · exfalso
          rw [hy_neg, hq3] at hyq_pos
          norm_num at hyq_pos
      exact ⟨hp2, hq3, hx_class, hy_eq⟩
    · have hyq_neg : y ^ q < 0 := by omega
      have hxp_neg : x ^ p < 0 := by omega
      have hxcast : ((x.natAbs ^ p : ℕ) : ℤ) = -(x ^ p) := by
        rw [← Int.natAbs_pow, ← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      have hycast : ((y.natAbs ^ q : ℕ) : ℤ) = -(y ^ q) := by
        rw [← Int.natAbs_pow, ← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      have hcast_add :
          ((y.natAbs ^ q : ℕ) : ℤ) = ((x.natAbs ^ p : ℕ) : ℤ) + 1 := by
        rw [hycast, hxcast]
        omega
      have hnat_add : y.natAbs ^ q = x.natAbs ^ p + 1 := by
        exact_mod_cast hcast_add
      have hnat_sub : y.natAbs ^ q - x.natAbs ^ p = 1 := by omega
      have hcat := Catalan.catalans_conjecture q p y.natAbs x.natAbs
        (by omega) (by omega) hyabs_pos hxabs_pos hnat_sub
      rcases hcat with ⟨hq2, hp3, hy3, hx2⟩
      rw [hq2] at hyq_neg
      have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      omega

end Catalan
