module

public import Catalan.Stickelberger.MinusDefs

/-!
# `Catalan.Stickelberger.MinusElement`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma minus_element_ne_zero (hp2 : p ≠ 2) :
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1 : R p K) ≠ 0 := by
  have hs1 : σ p K 1 = 1 := by
    unfold σ
    exact map_one _
  have hiota_ne : ι p K ≠ 1 := by
    intro hi
    have hsig : σ p K (-1 : (ZMod p)ˣ) = σ p K 1 := by
      simpa only [ι, hi, hs1]
    have hunit : (-1 : (ZMod p)ˣ) = 1 := (σ_bijective p K).1 hsig
    have hzmod : (-1 : ZMod p) = 1 :=
      congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hunit
    have htwozero : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = 1 + 1 := by ring
        _ = (-1 : ZMod p) + 1 := by rw [hzmod]
        _ = 0 := by ring
    have hpdiv : p ∣ (2 : ℕ) := by
      have htwozero' : ((2 : ℤ) : ZMod p) = 0 := by simpa using htwozero
      exact Int.natCast_dvd_natCast.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp htwozero')
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hpone | hptwo
    · exact (Fact.out : p.Prime).ne_one hpone
    · exact hp2 hptwo
  intro he
  have hc := congrArg (fun T : R p K => T.coeff (1 : G p K)) he
  simp only [MonoidAlgebra.coeff_zero, MonoidAlgebra.coeff_sub,
    MonoidAlgebra.coeff_single] at hc
  change (fun₀ | (1 : G p K) => (1 : ℤ)) (1 : G p K) -
      (fun₀ | ι p K => (1 : ℤ)) (1 : G p K) = 0 at hc
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hiota_ne)] at hc
  norm_num at hc

lemma minus_element_size (hp2 : p ≠ 2) :
    size p K (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1) = 2 := by
  let E : R p K := MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1
  have hne : E ≠ 0 := by
    dsimp [E]
    exact minus_element_ne_zero p K hp2
  have hweight : weight p K E = 0 := by
    dsimp [E]
    rw [weight_sub, weight_single, weight_single]
    norm_num
  have hle : size p K E ≤ 2 := by
    have hs := size_sub_le p K (MonoidAlgebra.single 1 1)
      (MonoidAlgebra.single (ι p K) 1)
    rw [size_single, size_single] at hs
    norm_num at hs ⊢
    exact hs
  have hge : 2 ≤ size p K E := by
    by_contra hlt
    have hlt' : (size p K E : ℝ) < 2 := by exact_mod_cast (show size p K E < 2 by omega)
    have hz := aug_size_lt_two p K E hweight hlt'
    exact hne hz
  have hEq : size p K E = 2 := by omega
  exact hEq

end Catalan
