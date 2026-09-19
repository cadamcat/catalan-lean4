import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
Arithmetic prerequisites for the Gauss valuation formula. The valuation hypotheses
were identified by reading xroblot/SKW, `SKW/Stickelberger/valGauss.lean`, revision
4db8676808a63d892a8f36ead11308ca8dd58520. The proofs here were independently written:
the exact-value step uses digit complementation. No SKW module is imported.
-/

namespace Catalan.Stickelberger

/-- The digit sum obeys Euclidean division even at zero. -/
theorem digitSum_div (b n : ℕ) (hb : 1 < b) :
    (b.digits n).sum = n % b + (b.digits (n / b)).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_eq_cons_digits_div hb hn, List.sum_cons]

/-- Complementing a number in an `f`-digit block complements every digit. -/
theorem digitSum_complement (b f n : ℕ) (hb : 1 < b) (hn : n < b ^ f) :
    (b.digits n).sum + (b.digits (b ^ f - 1 - n)).sum = f * (b - 1) := by
  induction f generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      simp [this]
  | succ f ih =>
      have hb0 : 0 < b := by omega
      have hpow : 0 < b ^ f := Nat.pow_pos hb0
      have hr : n % b < b := Nat.mod_lt n hb0
      have hq : n / b < b ^ f := by
        apply (Nat.div_lt_iff_lt_mul hb0).mpr
        simpa [Nat.pow_succ] using hn
      have hdecomp := Nat.mod_add_div n b
      have hc : b ^ (f + 1) - 1 - n =
          (b - 1 - n % b) + b * (b ^ f - 1 - n / b) := by
        rw [Nat.pow_succ]
        have hq' : n / b ≤ b ^ f - 1 := by omega
        have hr' : n % b ≤ b - 1 := by omega
        have hA := Nat.sub_add_cancel hq'
        have hB := Nat.sub_add_cancel hr'
        have hC := Nat.sub_add_cancel (show 1 ≤ b ^ f by omega)
        have hD := Nat.sub_add_cancel (show 1 ≤ b by omega)
        have hE := Nat.sub_add_cancel (show 1 ≤ b ^ f * b by nlinarith)
        have hF := Nat.sub_add_cancel (show n ≤ b ^ f * b - 1 by
          rw [Nat.pow_succ] at hn
          omega)
        nlinarith
      have hsmall : b - 1 - n % b < b := by omega
      rw [digitSum_div b n hb, digitSum_div b (b ^ (f + 1) - 1 - n) hb, hc]
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall,
        Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt hsmall, zero_add]
      have hi := ih (n / b) hq
      rw [Nat.succ_mul]
      omega

/-- Frobenius invariance and subadditivity bound a normalized valuation by digit sum. -/
theorem valuation_le_digitSum (v : ℕ → ℕ) (b : ℕ)
    (hzero : v 0 = 0) (hone : v 1 ≤ 1)
    (hadd : ∀ a c, v (a + c) ≤ v a + v c)
    (hfrob : ∀ a, v (b * a) = v a) (n : ℕ) :
    v n ≤ (b.digits n).sum := by
  have hlinear : ∀ a, v a ≤ a := by
    intro a
    induction a with
    | zero => omega
    | succ a ih =>
        have := hadd a 1
        omega
  have hlist : ∀ ds : List ℕ, v (Nat.ofDigits b ds) ≤ ds.sum := by
    intro ds
    induction ds with
    | nil => simpa using hzero.le
    | cons d ds ih =>
        rw [Nat.ofDigits_cons, List.sum_cons]
        exact (hadd _ _).trans (Nat.add_le_add (hlinear d) (by simpa [hfrob] using ih))
  simpa only [Nat.ofDigits_digits] using hlist (b.digits n)

/-- The arithmetic part of Stickelberger's valuation argument.
The four valuation identities are explicit inputs; this does not construct a Gauss sum. -/
theorem valuation_eq_digitSum (v : ℕ → ℕ) (b f : ℕ) (hb : 1 < b)
    (hzero : v 0 = 0) (hone : v 1 ≤ 1)
    (hadd : ∀ a c, v (a + c) ≤ v a + v c)
    (hfrob : ∀ a, v (b * a) = v a)
    (hpair : ∀ a, 0 < a → a < b ^ f - 1 →
      v a + v (b ^ f - 1 - a) = f * (b - 1))
    (n : ℕ) (hn : n < b ^ f - 1) :
    v n = (b.digits n).sum := by
  by_cases hn0 : n = 0
  · simp [hn0, hzero]
  · have h1 := valuation_le_digitSum v b hzero hone hadd hfrob n
    have h2 := valuation_le_digitSum v b hzero hone hadd hfrob (b ^ f - 1 - n)
    have h3 := digitSum_complement b f n hb (by omega)
    have h4 := hpair n (by omega) hn
    omega

/-- Extended-natural valuations have the same digit bound, which also proves finiteness. -/
theorem enatValuation_le_digitSum (v : ℕ → ℕ∞) (b : ℕ)
    (hzero : v 0 = 0) (hone : v 1 ≤ 1)
    (hadd : ∀ a c, v (a + c) ≤ v a + v c)
    (hfrob : ∀ a, v (b * a) = v a) (n : ℕ) :
    v n ≤ ((b.digits n).sum : ℕ) := by
  have hlinear : ∀ a, v a ≤ (a : ℕ∞) := by
    intro a
    induction a with
    | zero => simpa using hzero.le
    | succ a ih =>
        exact (hadd a 1).trans (by simpa using add_le_add ih hone)
  have hlist : ∀ ds : List ℕ, v (Nat.ofDigits b ds) ≤ (ds.sum : ℕ∞) := by
    intro ds
    induction ds with
    | nil => simpa using hzero.le
    | cons d ds ih =>
        rw [Nat.ofDigits_cons, List.sum_cons, Nat.cast_add]
        exact (hadd _ _).trans (add_le_add (hlinear d) (by simpa [hfrob] using ih))
  simpa only [Nat.ofDigits_digits] using hlist (b.digits n)

/-- An `emultiplicity`-compatible version of the arithmetic valuation criterion. -/
theorem enatValuation_eq_digitSum (v : ℕ → ℕ∞) (b f : ℕ) (hb : 1 < b)
    (hzero : v 0 = 0) (hone : v 1 ≤ 1)
    (hadd : ∀ a c, v (a + c) ≤ v a + v c)
    (hfrob : ∀ a, v (b * a) = v a)
    (hpair : ∀ a, 0 < a → a < b ^ f - 1 →
      v a + v (b ^ f - 1 - a) = (f * (b - 1) : ℕ))
    (n : ℕ) (hn : n < b ^ f - 1) :
    v n = ((b.digits n).sum : ℕ) := by
  have hfinite : ∀ a, v a ≠ ⊤ := fun a ↦
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (enatValuation_le_digitSum v b hzero hone hadd hfrob a)
  have hz : (v 0).toNat = 0 := by simp [hzero]
  have ho : (v 1).toNat ≤ 1 := ENat.toNat_le_of_le_natCast (by simpa using hone)
  have ha : ∀ a c, (v (a + c)).toNat ≤ (v a).toNat + (v c).toNat := by
    intro a c
    have h := ENat.toNat_le_toNat (hadd a c) (by simp [hfinite a, hfinite c])
    simpa only [ENat.toNat_add (hfinite a) (hfinite c)] using h
  have hf : ∀ a, (v (b * a)).toNat = (v a).toNat := fun a ↦ congrArg ENat.toNat (hfrob a)
  have hp : ∀ a, 0 < a → a < b ^ f - 1 →
      (v a).toNat + (v (b ^ f - 1 - a)).toNat = f * (b - 1) := by
    intro a ha hlt
    have h := congrArg ENat.toNat (hpair a ha hlt)
    simpa only [ENat.toNat_add (hfinite a) (hfinite _), ENat.toNat_natCast] using h
  have he := valuation_eq_digitSum (fun a ↦ (v a).toNat) b f hb hz ho ha hf hp n hn
  calc
    v n = ((v n).toNat : ℕ∞) := (ENat.natCast_toNat (hfinite n)).symm
    _ = ((b.digits n).sum : ℕ) := congrArg (fun a : ℕ ↦ (a : ℕ∞)) he

end Catalan.Stickelberger
