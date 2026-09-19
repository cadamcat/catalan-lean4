import Catalan.Wieferich.Frobenius
import Catalan.Wieferich.Core

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Primary

lemma square_dvd_pow_sub_pow (A : Type*) [CommRing A] (q : ℕ) (hq : q.Prime)
    (a b : A) (hab : (q : A) ∣ a - b) :
    (q : A) ^ 2 ∣ a ^ q - b ^ q := by
  obtain ⟨t, ht⟩ := hab
  have ha : a = (q : A) * t + b := by
    calc
      a = (a - b) + b := by ring
      _ = (q : A) * t + b := by rw [ht]
  have hpow : (q : A) ^ 2 ∣ ((q : A) * t) ^ q := by
    rw [mul_pow]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (q : A) hq.two_le) _
  have hlin : (q : A) ^ 2 ∣ (q : A) * ((q : A) * t) := by
    exact ⟨t, by ring⟩
  have hmain := Nat.Prime.dvd_add_pow_sub_pow_of_dvd
    ((q : A) * t) b hq hpow hlin
  simpa [ha] using hmain

lemma prime_dvd_of_dvd_pow
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (q : ℕ) (hq : q.Prime) (hpq : p ≠ q) (a : 𝓞 K)
    (ha : (q : 𝓞 K) ∣ a ^ q) : (q : 𝓞 K) ∣ a := by
  obtain ⟨F, hF⟩ := A1e.cyclotomic_frobenius_lift p K q hq hpq
  have hFa : (q : 𝓞 K) ∣ F a := by
    have hsub := dvd_sub ha (hF a)
    simpa only [sub_sub_cancel] using hsub
  obtain ⟨c, hc⟩ := hFa
  refine ⟨F.symm c, ?_⟩
  have hmap := congrArg F.symm hc
  simpa only [map_mul, map_natCast, RingEquiv.symm_apply_apply] using hmap

end Catalan.Primary
