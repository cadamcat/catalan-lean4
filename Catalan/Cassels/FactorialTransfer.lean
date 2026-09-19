import Catalan.Cassels.DenominatorDefs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Catalan

/-- A divisor of `k!` coprime to `q` divides the signed numerator product. -/
lemma cassels_factorial_divisor_dvd_numProd (p q d k : Nat) (hd : 0 < d)
    (hdk : d ∣ k.factorial) (hqd : q.Coprime d) :
    (d : Int) ∣ casselsNumProd p q k := by
  obtain ⟨s, hs⟩ := Int.mod_coprime hqd
  let r : Int := (p : Int) * s
  have hpr : (p : Int) ≡ (q : Int) * r [ZMOD (d : Int)] := by
    simpa [r, mul_assoc, mul_comm, mul_left_comm] using (hs.mul_left (p : Int)).symm
  have hprod : casselsNumProd p q k ≡
      ∏ i ∈ Finset.range k, (-(q : Int)) * (-r + (i : Int)) [ZMOD (d : Int)] := by
    unfold casselsNumProd
    apply Int.ModEq.prod
    intro i hi
    convert hpr.sub_right ((i : Int) * (q : Int)) using 1
    ring
  have hdf : (d : Int) ∣ (k.factorial : Int) := by
    exact_mod_cast hdk
  have hfac : (d : Int) ∣ ∏ i ∈ Finset.range k, (-r + (i : Int)) :=
    hdf.trans (Nat.factorial_coe_dvd_prod k (-r))
  have hscaled : (d : Int) ∣
      ∏ i ∈ Finset.range k, (-(q : Int)) * (-r + (i : Int)) := by
    rw [Finset.prod_mul_distrib]
    exact dvd_mul_of_dvd_right hfac _
  exact hprod.dvd_iff.mpr hscaled

end Catalan

#print axioms Catalan.cassels_factorial_divisor_dvd_numProd
