module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Tactic

/-! Conversion of a base-b digit sum into a cyclic sum of residues. -/

/-!
# `Catalan.Stickelberger.DigitResidue`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators

namespace Catalan.Stickelberger

private lemma digitResidue_unroll (b m : ℕ) (r t : ℕ → ℕ)
    (hrec : ∀ i, b * r i = m * t i + r (i + 1)) (f : ℕ) :
    b ^ f * r 0 = m * (∑ i ∈ Finset.range f, t i * b ^ (f - 1 - i)) + r f := by
  induction f with
  | zero => simp
  | succ f ih =>
      rw [Nat.pow_succ', mul_assoc, ih]
      rw [Nat.mul_add, hrec f]
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, mul_one]
      have hsum :
          (∑ i ∈ Finset.range f, t i * b ^ (f - i)) =
            ∑ i ∈ Finset.range f, (t i * b ^ (f - 1 - i)) * b := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < f := Finset.mem_range.mp hi
        have hsub : f - i = (f - 1 - i) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        ring
      rw [hsum]
      rw [← Finset.sum_mul]
      simp only [Nat.sub_self, pow_zero, one_mul]
      ring

private lemma digitResidue_sum_rev (f : ℕ) (g : Fin f → ℕ) :
    (List.ofFn (fun i : Fin f ↦ g (Fin.rev i))).sum = ∑ i : Fin f, g i := by
  rw [List.sum_ofFn]
  exact Finset.sum_bijective Fin.rev Fin.rev_involutive.bijective
    (fun _ ↦ by simp) (fun _ _ ↦ rfl)

private lemma digitResidue_ofDigits_ofFn (b f : ℕ) (g : Fin f → ℕ) :
    Nat.ofDigits b (List.ofFn g) = ∑ i : Fin f, g i * b ^ i.val := by
  induction f with
  | zero => simp
  | succ f ih =>
      rw [List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ]
      rw [ih]
      simp only [Fin.val_zero, pow_zero, mul_one]
      have htail :
          (∑ i : Fin f, g i.succ * b ^ i.succ.val) =
            b * ∑ i : Fin f, g i.succ * b ^ i.val := by
        rw [Finset.mul_sum Finset.univ (fun i : Fin f ↦ g i.succ * b ^ i.val) b]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Fin.val_succ, Nat.pow_succ]
        ring
      rw [htail]

private lemma digitResidue_weight (b f : ℕ) (t : ℕ → ℕ) :
    (∑ i ∈ Finset.range f, t i * b ^ (f - 1 - i)) =
      ∑ i : Fin f, t (Fin.rev i) * b ^ i.val := by
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ t i * b ^ (f - 1 - i)) f]
  exact Finset.sum_bijective Fin.rev Fin.rev_involutive.bijective
    (fun _ ↦ by simp) (fun i _ ↦ by
      simp only [Fin.rev_rev]
      congr 2
      dsimp [Fin.rev]
      omega)

private lemma digitResidue_sum_shift (f : ℕ) (r : ℕ → ℕ) (hcycle : r f = r 0) :
    (∑ i ∈ Finset.range f, r (i + 1)) = ∑ i ∈ Finset.range f, r i := by
  rw [Finset.sum_range, Finset.sum_range]
  have hs := Fin.sum_univ_succ (fun j : Fin (f + 1) ↦ r j.val)
  have hc := Fin.sum_univ_castSucc (fun j : Fin (f + 1) ↦ r j.val)
  have heq :
      r 0 + (∑ i : Fin f, r i.succ.val) =
        (∑ i : Fin f, r i.castSucc.val) + r f := by
    calc
      r 0 + (∑ i : Fin f, r i.succ.val) = ∑ j : Fin (f + 1), r j.val := by
        simpa only [Fin.val_zero, Fin.val_succ] using hs.symm
      _ = (∑ i : Fin f, r i.castSucc.val) + r f := by
        simpa only [Fin.val_castSucc, Fin.val_last] using hc
  simp only [Fin.val_castSucc, Fin.val_succ] at heq
  omega

private lemma digitResidue_sumrec (b m f : ℕ) (r t : ℕ → ℕ)
    (hrec : ∀ i, b * r i = m * t i + r (i + 1)) :
    b * (∑ i ∈ Finset.range f, r i) =
      m * (∑ i ∈ Finset.range f, t i) + ∑ i ∈ Finset.range f, r (i + 1) := by
  rw [Finset.mul_sum (Finset.range f) (fun i ↦ r i) b]
  rw [Finset.mul_sum (Finset.range f) (fun i ↦ t i) m]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl]
  intro i hi
  exact hrec i

private lemma digitResidue_hmod (b m a i : ℕ) :
    (a * b ^ (i + 1)) % m = (b * ((a * b ^ i) % m)) % m := by
  calc
    (a * b ^ (i + 1)) % m = (a * b ^ i * b) % m := by
      rw [pow_succ']
      congr 1
      ring
    _ = ((a * b ^ i) % m * (b % m)) % m := by
      rw [Nat.mul_mod]
    _ = ((b % m) * ((a * b ^ i) % m)) % m := by
      congr 1
      ring
    _ = (b * ((a * b ^ i) % m)) % m := by
      symm
      simpa only [Nat.mod_mod] using Nat.mul_mod b ((a * b ^ i) % m) m

theorem mul_digitSum_eq_mul_sum_mod (b f m d a : ℕ)
    (hb : 1 < b) (hf : 0 < f) (hm : 1 < m)
    (hdm : d * m = b ^ f - 1) (ha : a < m) :
    m * (b.digits (d * a)).sum =
      (b - 1) * ∑ i ∈ Finset.range f, (a * b ^ i) % m := by
  have hb0 : 0 < b := by omega
  have hm0 : 0 < m := by omega
  let r : ℕ → ℕ := fun i ↦ (a * b ^ i) % m
  let t : ℕ → ℕ := fun i ↦ b * r i / m
  have hr_lt : ∀ i, r i < m := by
    intro i
    exact Nat.mod_lt _ hm0
  have hrec : ∀ i, b * r i = m * t i + r (i + 1) := by
    intro i
    dsimp [r, t]
    rw [digitResidue_hmod]
    have h := Nat.div_add_mod' (b * ((a * b ^ i) % m)) m
    nlinarith
  have hrf : r f = a := by
    dsimp [r]
    have hpow0 : 0 < b ^ f := Nat.pow_pos hb0
    have hpow : b ^ f = 1 + (b ^ f - 1) := by omega
    have hmul : a * b ^ f = a + m * (d * a) := by
      rw [hpow, Nat.mul_add, ← hdm]
      ring
    rw [hmul]
    have hcomm : m * (d * a) = (d * a) * m := by ring
    rw [hcomm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have hunroll := digitResidue_unroll b m r t hrec f
  have hpow_d : b ^ f = 1 + d * m := by
    have hpow0 : 0 < b ^ f := Nat.pow_pos hb0
    have hpow : b ^ f = 1 + (b ^ f - 1) := by omega
    rw [hpow, ← hdm]
  have hexpand : d * a = ∑ i ∈ Finset.range f, t i * b ^ (f - 1 - i) := by
    dsimp [r] at hunroll hrf
    rw [hrf] at hunroll
    rw [hpow_d] at hunroll
    simp [Nat.mod_eq_of_lt ha] at hunroll
    nlinarith [hunroll]
  have ht_lt : ∀ i, t i < b := by
    intro i
    apply (Nat.div_lt_iff_lt_mul hm0).2
    exact Nat.mul_lt_mul_of_pos_left (hr_lt i) (by omega)
  let L : List ℕ := List.ofFn (fun i : Fin f ↦ t (Fin.rev i))
  have hLlen : L.length = f := by
    simp [L]
  have hLmem : ∀ x ∈ L, x < b := by
    intro x hx
    change x ∈ List.ofFn (fun i : Fin f ↦ t (Fin.rev i)) at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ht_lt (Fin.rev i)
  have hLnum : Nat.ofDigits b L = d * a := by
    have hnum := digitResidue_ofDigits_ofFn b f (fun i : Fin f ↦ t (Fin.rev i))
    dsimp [L]
    calc
      Nat.ofDigits b (List.ofFn (fun i : Fin f ↦ t (Fin.rev i))) =
          ∑ i : Fin f, t (Fin.rev i) * b ^ i.val := hnum
      _ = ∑ i ∈ Finset.range f, t i * b ^ (f - 1 - i) :=
        (digitResidue_weight b f t).symm
      _ = d * a := hexpand.symm
  have hLdigits : (b.digits (Nat.ofDigits b L)).sum = L.sum := by
    apply Nat.sum_digits_ofDigits_eq_sum hb
    exact ⟨hLlen, hLmem⟩
  have hdsum : (b.digits (d * a)).sum = ∑ i : Fin f, t i := by
    rw [← hLnum, hLdigits]
    simpa [L] using digitResidue_sum_rev f (fun i : Fin f ↦ t i)
  have hr0 : r 0 = a := by
    dsimp [r]
    simp [Nat.mod_eq_of_lt ha]
  have hshift :
      (∑ i ∈ Finset.range f, r (i + 1)) = ∑ i ∈ Finset.range f, r i := by
    apply digitResidue_sum_shift f r
    exact hrf.trans hr0.symm
  have hsumrec := digitResidue_sumrec b m f r t hrec
  have hsumrec' :
      b * (∑ i ∈ Finset.range f, r i) =
        m * (∑ i ∈ Finset.range f, t i) + ∑ i ∈ Finset.range f, r i := by
    rw [hshift] at hsumrec
    exact hsumrec
  have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
  have hdsum_range :
      (b.digits (d * a)).sum = ∑ i ∈ Finset.range f, t i := by
    rw [hdsum, Fin.sum_univ_eq_sum_range]
  have hfinal :
      m * (∑ i ∈ Finset.range f, t i) =
        (b - 1) * (∑ i ∈ Finset.range f, r i) := by
    have hmul := congrArg (fun x ↦ x * (∑ i ∈ Finset.range f, r i)) hbsub
    have heq := hmul.trans hsumrec'
    nlinarith [heq]
  calc
    m * (b.digits (d * a)).sum = m * (∑ i ∈ Finset.range f, t i) := by rw [hdsum_range]
    _ = (b - 1) * (∑ i ∈ Finset.range f, r i) := hfinal
    _ = (b - 1) * ∑ i ∈ Finset.range f, (a * b ^ i) % m := by rfl

end Catalan.Stickelberger

