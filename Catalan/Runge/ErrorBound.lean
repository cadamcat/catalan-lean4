import Catalan.Runge.Definitions

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

lemma D_bounds (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q) (k m : ℕ) :
    D q (k + 1) ≥ D q k + 1 ∧ 6 * D q m ≤ 7 * m := by
  let instFactQ : Fact q.Prime := ⟨hq⟩
  constructor
  · simp only [D, casselsDenExp, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k)]
    omega
  · rcases eq_or_ne m 0 with rfl | hm0
    · simp [D, casselsDenExp]
    · have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero q hm0
      have hq6 : 6 ≤ q - 1 := by omega
      have h6v : 6 * padicValNat q m.factorial ≤
          (q - 1) * padicValNat q m.factorial := Nat.mul_le_mul_right _ hq6
      dsimp [D, casselsDenExp]
      omega

lemma runge_numeric : (41 / 20 : ℚ) ^ 12 < (7 : ℚ) ^ 5 := by norm_num

lemma error_lt_one (p q m : ℕ) (X : ℝ) (hq : q.Prime)
    (hq7 : 7 ≤ q) (hm : 0 < m) (hmp : 2 * m ≤ p - 1)
    (hX : (q : ℝ) ^ (p - 1) < X) : errorBound q m X < 1 := by
  have hD : 6 * D q m ≤ 7 * m := (D_bounds q hq hq7 0 m).2
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hq7R : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hpmin : 2 ≤ p - 1 := by omega
  have hqpow49 : (49 : ℝ) ≤ (q : ℝ) ^ (p - 1) := by
    calc
      (49 : ℝ) = (7 : ℝ) ^ 2 := by norm_num
      _ ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hq7R 2
      _ ≤ (q : ℝ) ^ (p - 1) := pow_le_pow_right₀ hqR hpmin
  have hX49 : (49 : ℝ) < X := hqpow49.trans_lt hX
  have hXpos : 0 < X := by linarith
  have hX1 : 0 < X - 1 := by linarith
  have hinv : X⁻¹ < (1 / 49 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hX49
  have hr : (40 / 41 : ℝ) < 1 - X⁻¹ := by
    nlinarith
  have hrpos : 0 < (1 - X⁻¹ : ℝ) := by linarith
  have hchoosePow : Nat.choose (2*m) (m+1) ≤ 2^(2*m-1) := by
    have hh0 := Nat.choose_succ_le_two_pow (2*m-1) (m+1)
    simpa only [show 2*m-1+1 = 2*m by omega] using hh0
  have hchooseR : (Nat.choose (2*m) (m+1) : ℝ) ≤
      (2 : ℝ)^(2*m-1) := by exact_mod_cast hchoosePow
  have hconst : (41 / 20 : ℝ)^12 < (7 : ℝ)^5 := by norm_num
  have hbase : (41 / 20 : ℝ)^12 < (q : ℝ)^5 := by
    exact hconst.trans_le (pow_le_pow_left₀ (by norm_num) hq7R 5)
  have hpowconst : (41 / 20 : ℝ)^(12*m) < (q : ℝ)^(5*m) := by
    calc
      (41 / 20 : ℝ)^(12*m) = ((41 / 20 : ℝ)^12)^m := by rw [pow_mul]
      _ < ((q : ℝ)^5)^m := pow_lt_pow_left₀ hbase (by positivity) (by positivity)
      _ = (q : ℝ)^(5*m) := by rw [pow_mul]
  have hqD : (q : ℝ)^(6 * D q m) ≤ (q : ℝ)^(7*m) :=
    pow_le_pow_right₀ hqR hD
  let A : ℝ := (q : ℝ) ^ D q m * (41 / 20 : ℝ) ^ (2*m)
  have hA6 : A^6 < ((q : ℝ)^(2*m))^6 := by
    dsimp [A]
    calc
      ((q : ℝ) ^ D q m * (41 / 20 : ℝ) ^ (2*m)) ^ 6 =
          (q : ℝ)^(6 * D q m) * (41 / 20 : ℝ)^(12*m) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
            congr 1 <;> ring
      _ < (q : ℝ)^(7*m) * (q : ℝ)^(5*m) :=
        (calc
          (q : ℝ)^(6 * D q m) * (41 / 20 : ℝ)^(12*m) ≤
              (q : ℝ)^(7*m) * (41 / 20 : ℝ)^(12*m) :=
            mul_le_mul_of_nonneg_right hqD (by positivity)
          _ < (q : ℝ)^(7*m) * (q : ℝ)^(5*m) :=
            mul_lt_mul_of_pos_left hpowconst (by positivity))
      _ = ((q : ℝ)^(2*m))^6 := by
        rw [← pow_add, pow_mul]
        rw [show 7*m + 5*m = 2*m*6 by ring]
        simp only [pow_mul]
  have hA : A < (q : ℝ)^(2*m) :=
    lt_of_pow_lt_pow_left₀ 6 (by positivity) hA6
  have hcoef :
      (2 : ℝ)^(2*m-1) * (41 / 40 : ℝ)^(2*m+1) <
        (41 / 20 : ℝ)^(2*m) := by
    calc
      (2 : ℝ)^(2*m-1) * (41 / 40 : ℝ)^(2*m+1) =
          (2 : ℝ)^(2*m-1) * ((41 / 40 : ℝ)^(2*m) * (41 / 40 : ℝ)) := by
            rw [pow_add, pow_one]
      _ < (2 : ℝ)^(2*m-1) * ((41 / 40 : ℝ)^(2*m) * 2) := by
            gcongr
            norm_num
      _ = (41 / 20 : ℝ)^(2*m) := by
            calc
              (2 : ℝ)^(2*m-1) * ((41 / 40 : ℝ)^(2*m) * 2) =
                  ((2 : ℝ)^(2*m-1) * 2) * (41 / 40 : ℝ)^(2*m) := by ring
              _ = (2 : ℝ)^(2*m) * (41 / 40 : ℝ)^(2*m) := by
                have he : 2*m - 1 + 1 = 2*m := by omega
                calc
                  ((2 : ℝ)^(2*m-1) * 2) * (41 / 40 : ℝ)^(2*m) =
                      ((2 : ℝ)^(2*m-1) * (2 : ℝ)^1) *
                        (41 / 40 : ℝ)^(2*m) := by norm_num
                  _ = (2 : ℝ)^((2*m-1)+1) * (41 / 40 : ℝ)^(2*m) := by
                    rw [← pow_add]
                  _ = (2 : ℝ)^(2*m) * (41 / 40 : ℝ)^(2*m) := by rw [he]
              _ = (41 / 20 : ℝ)^(2*m) := by
                rw [← mul_pow]
                norm_num
  let ratio : ℝ := (41 / 40 : ℝ)^(2*m+1)
  have hratio : 0 < ratio := by positivity
  have hnumRatio :
      ((q : ℝ)^D q m * (Nat.choose (2*m) (m+1) : ℝ)) * ratio <
        (q : ℝ)^(2*m) := by
    calc
      ((q : ℝ)^D q m * (Nat.choose (2*m) (m+1) : ℝ)) * ratio ≤
          ((q : ℝ)^D q m * (2 : ℝ)^(2*m-1)) * ratio := by
            gcongr
      _ < ((q : ℝ)^D q m * (41 / 20 : ℝ)^(2*m)) := by
            dsimp [ratio]
            calc
              ((q : ℝ)^D q m * (2 : ℝ)^(2*m-1)) *
                  (41 / 40 : ℝ)^(2*m+1) =
                  (q : ℝ)^D q m *
                    ((2 : ℝ)^(2*m-1) * (41 / 40 : ℝ)^(2*m+1)) := by ring
              _ < (q : ℝ)^D q m * (41 / 20 : ℝ)^(2*m) :=
                mul_lt_mul_of_pos_left hcoef (by positivity)
      _ = A := by rfl
      _ < (q : ℝ)^(2*m) := hA
  have hqpowX : (q : ℝ)^(2*m) < X := by
    exact (pow_le_pow_right₀ hqR hmp).trans_lt hX
  have hnumX :
      ((q : ℝ)^D q m * (Nat.choose (2*m) (m+1) : ℝ)) * ratio < X :=
    hnumRatio.trans hqpowX
  have hrpow : (40 / 41 : ℝ)^(2*m+1) ≤ (1 - X⁻¹)^(2*m+1) :=
    pow_le_pow_left₀ (by norm_num) hr.le _
  have hratio_inv :
      (40 / 41 : ℝ)^(2*m+1) * ratio = 1 := by
    dsimp [ratio]
    rw [← mul_pow]
    norm_num
  have hXle : X ≤ ((1 - X⁻¹)^(2*m+1) * X) * ratio := by
    calc
      X = X * 1 := by ring
      _ = X * ((40 / 41 : ℝ)^(2*m+1) * ratio) := by rw [hratio_inv]
      _ = (X * (40 / 41 : ℝ)^(2*m+1)) * ratio := by ring
      _ ≤ (X * (1 - X⁻¹)^(2*m+1)) * ratio := by
        gcongr
      _ = ((1 - X⁻¹)^(2*m+1) * X) * ratio := by ring
  have hden :
      (q : ℝ)^D q m * (Nat.choose (2*m) (m+1) : ℝ) <
        (1 - X⁻¹)^(2*m+1) * X := by
    apply lt_of_mul_lt_mul_right _ (le_of_lt hratio)
    exact hnumX.trans_le hXle
  rw [errorBound]
  apply (div_lt_iff₀ (mul_pos (pow_pos hrpos _) hXpos)).2
  simpa using hden


end Catalan.Runge
