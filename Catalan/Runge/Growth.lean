import Catalan.Cassels.Factorization
import Catalan.Cassels.Hyyro

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Runge

lemma cassels_growth (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq7 : 7 ≤ q) (hqp : q < p) (x y : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    (q : ℝ) ^ (p - 1) < (|x| : ℝ) := by
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hqx : (q : ℤ) ∣ x :=
    cassels_easy_q_dvd_x p q hp hq hp2 hq2 hqp x y hx hy h
  have hlarge := cassels_lower_bound p q hp hq hp2 hq2 hqp x y hx hy h hqx
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hstrict : (q : ℤ) ^ (p - 1) < |x| :=
    (lt_add_of_pos_right ((q : ℤ) ^ (p - 1)) hqpos).trans_le hlarge
  exact_mod_cast hstrict

end Catalan.Runge
