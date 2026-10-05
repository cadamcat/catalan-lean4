module

public import Catalan.Runge.Definitions
public import Catalan.Wieferich.Frobenius

/-!
# `Catalan.Runge.ReducedQuotient`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private lemma dvd_of_dvd_qpow (q : ℕ) (hq : q.Prime) (hpq : p ≠ q)
    (a : 𝓞 K) (j : ℕ) (h : (q : 𝓞 K) ∣ a ^ (q ^ j)) :
    (q : 𝓞 K) ∣ a := by
  obtain ⟨F, hF⟩ := A1e.cyclotomic_frobenius_lift p K q hq hpq
  induction j with
  | zero => simpa using h
  | succ j ih =>
      let b := a ^ (q ^ j)
      have hpow : (q : 𝓞 K) ∣ b ^ q := by
        have he : q ^ (Nat.succ j) = q ^ j * q := by rw [pow_succ]
        simpa [b, he, pow_mul] using h
      have hFb : (q : 𝓞 K) ∣ F b := by
        have hh := dvd_sub hpow (hF b)
        simpa only [sub_sub_cancel] using hh
      obtain ⟨c, hc⟩ := hFb
      have hb : (q : 𝓞 K) ∣ b := by
        refine ⟨F.symm c, ?_⟩
        simpa only [map_mul, map_natCast, RingEquiv.symm_apply_apply] using
          congrArg F.symm hc
      exact ih (by simpa [b] using hb)

lemma cyclotomic_prime_dvd_of_dvd_pow (q : ℕ) (hq : q.Prime) (hpq : p ≠ q)
    (a : 𝓞 K) (n : ℕ) (h : (q : 𝓞 K) ∣ a ^ n) : (q : 𝓞 K) ∣ a := by
  let j := Nat.clog q n
  have hnj : n ≤ q ^ j := by
    exact Nat.le_pow_clog hq.one_lt n
  obtain ⟨c, hc⟩ := h
  have hpow : (q : 𝓞 K) ∣ a ^ (q ^ j) := by
    refine ⟨c * a ^ (q ^ j - n), ?_⟩
    calc
      a ^ (q ^ j) = a ^ n * a ^ (q ^ j - n) := by
        rw [← pow_add, Nat.add_sub_of_le hnj]
      _ = (q : 𝓞 K) * c * a ^ (q ^ j - n) := by rw [hc]
      _ = (q : 𝓞 K) * (c * a ^ (q ^ j - n)) := by ring
  exact dvd_of_dvd_qpow p K q hq hpq a j hpow

lemma isReduced_cyclotomic_quotient (q : ℕ) (hq : q.Prime) (hpq : p ≠ q) :
    IsReduced (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := by
  let I : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hred : IsReduced (𝓞 K ⧸ I) := by
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := hx
    have hmem : a ^ n ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_pow] using hn
    have hdiv : (q : 𝓞 K) ∣ a ^ n :=
      Ideal.mem_span_singleton.mp hmem
    have hdiva := cyclotomic_prime_dvd_of_dvd_pow p K q hq hpq a n hdiv
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr hdiva
  simpa only [I] using hred

end Catalan.Runge
