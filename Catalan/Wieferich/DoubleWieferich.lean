module

public import Catalan.Wieferich.Minus
public import Catalan.Wieferich.LiftProduct
public import Catalan.Wieferich.Obstruction
public import Catalan.Wieferich.Arithmetic

/-!
# `Catalan.Wieferich.DoubleWieferich`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField
namespace Catalan
namespace A1e
section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

include K in
/-- Strong Cassels divisibility, proved in the p-th cyclotomic field. -/
lemma super_cassels_in_field
    (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (q : ℤ) ^ 2 ∣ x := by
  have hp := (Fact.out : p.Prime)
  have hqx := cassels_q_dvd_x p q hp hq hp2 hq2 x y hx hy h
  have hpow := minus_stick_qth p K q hq hp2 hq2 hpq x y hx hy h
    (ΘS p K 2) (theta_two_mem p K)
  change ∃ b : Kˣ,
    upow p K (xmζ p K x hp2) (testTheta p K) = b ^ q at hpow
  have hLift := liftProduct_qth p K q hq hp2 hq2 hpq x hpow
  have hobs := liftProduct_obstruction p K q hq hpq x hqx hLift
  exact square_dvd_x_from_obstruction p K q hq hp2 x hobs


end Cyclotomic

/-- Strong divisibility without a field parameter. -/
lemma super_cassels (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : (q : ℤ) ^ 2 ∣ x := by
  have instPrime : Fact p.Prime := ⟨hp⟩
  have instNeZero : NeZero p := ⟨hp.ne_zero⟩
  have instCyclo : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hpq := solution_primes_ne p q hp hq hp2 hq2 x y hx hy h
  exact super_cassels_in_field p (CyclotomicField p ℚ)
    q hq hp2 hq2 hpq x y hx hy h

/-- The direction furnished by Q(zeta_p) is p^(q-1)=1 modulo q^2. -/
lemma one_sided_wieferich (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    p ^ (q - 1) ≡ 1 [MOD q ^ 2] := by
  have hpq := solution_primes_ne p q hp hq hp2 hq2 x y hx hy h
  have hsq := super_cassels p q hp hq hp2 hq2 x y hx hy h
  obtain ⟨a, b, u, v, ha, hb, hu, hv, hfac, hrest⟩ :=
    cassels_factorization p q hp hq hp2 hq2 x y hx hy h
  exact wieferich_of_factorization p q hp hq hq2 hpq x a hsq hfac


end A1e

/-- Mihailescu's double Wieferich criterion, with the first and second conjuncts
in their prescribed order. -/
theorem double_wieferich (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    q ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ p ^ (q - 1) ≡ 1 [MOD q ^ 2] := by
  have hs := A1e.symmetry p q (hp.odd_of_ne_two hp2)
    (hq.odd_of_ne_two hq2) x y h
  constructor
  · exact A1e.one_sided_wieferich q p hq hp hq2 hp2
      (-y) (-x) (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hs
  · exact A1e.one_sided_wieferich p q hp hq hp2 hq2 x y hx hy h


end Catalan
