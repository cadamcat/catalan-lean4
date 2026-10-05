module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Tactic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Multiplicity

/-!
# `Catalan.Stickelberger.LocalGauss`

Part of the Catalan formalization.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Catalan.Stickelberger

/-! First-order integral trace Gauss sums. The field trace coefficient is
computed using Mathlib finite-field trace and unit power sums. Cyclotomic
reduction maps and uniformizer facts are explicit inputs. -/

lemma sum_inv_mul_pow {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 0 < n) :
    (∑ x : F, x⁻¹ * x ^ n) = ∑ x : Fˣ, (x : F) ^ (n - 1) := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
  simp only [inv_zero, zero_mul, zero_add]
  apply Fintype.sum_equiv unitsEquivNeZero.symm
  intro x
  change x.val⁻¹ * x.val ^ n = x.val ^ (n - 1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.succ_sub_one, pow_succ, ← mul_assoc, mul_comm x.val⁻¹,
    mul_assoc, inv_mul_cancel₀ x.property, mul_one]

/-- The coefficient of the linear term in the inverse-Teichmuller Gauss sum. -/
theorem sum_inv_mul_trace (k F : Type*) [Field k] [Fintype k]
    [Field F] [Fintype F] [Algebra k F] :
    (∑ x : F, x⁻¹ * algebraMap k F (Algebra.trace k F x)) = -1 := by
  classical
  simp_rw [FiniteField.algebraMap_trace_eq_sum_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hc : Nat.card k = Fintype.card k := Nat.card_eq_fintype_card
  simp_rw [hc, sum_inv_mul_pow _ (pow_pos Fintype.card_pos _),
    FiniteField.sum_pow_units]
  have hd : 0 < Module.finrank k F := Module.finrank_pos
  rw [← Nat.succ_pred_eq_of_pos hd, Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_self, dvd_zero, ↓reduceIte]
  have hz : ∑ i ∈ Finset.range (Module.finrank k F - 1),
      (if Fintype.card F - 1 ∣ Fintype.card k ^ (i + 1) - 1 then (-1 : F) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    apply Nat.not_dvd_of_pos_of_lt
    · exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) Fintype.one_lt_card)
    · rw [Module.card_eq_pow_finrank (K := k) (V := F)]
      apply Nat.sub_lt_sub_right (Nat.one_le_pow _ _ Fintype.card_pos)
      apply Nat.pow_lt_pow_right Fintype.one_lt_card
      simp only [Finset.mem_range] at hi
      omega
  simp only [Nat.pred_eq_sub_one, hz, zero_add]


lemma pow_eq_one_add_of_sub_one_sq_zero {B : Type*} [CommRing B]
    (z : B) (hz : (z - 1) ^ 2 = 0) (n : ℕ) :
    z ^ n = 1 + n * (z - 1) := by
  have hmul : (z - 1) * z = z - 1 := by
    have h : (z - 1) * z - (z - 1) = 0 := by linear_combination hz
    exact sub_eq_zero.mp h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one]
    calc
      (1 + (n : B) * (z - 1)) * z = z + n * ((z - 1) * z) := by ring
      _ = 1 + (n + 1) * (z - 1) := by rw [hmul]; ring

/-- An integral trace Gauss sum, with values in any commutative ring. -/
def integralTraceGaussSum {p : ℕ} [Fact p.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F] [CommRing A]
    (χ : MulChar F A) {ζ : A} (hζ : ζ ^ p = 1) : A :=
  gaussSum χ ((AddChar.zmodChar p hζ).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom)

/-- Reducing the actual finite Gauss sum to a ring where ζ−1 has square zero
leaves precisely its linear term. The inverse-character reduction determines
that coefficient to be minus one. -/
theorem integralTraceGaussSum_first_order {p : ℕ} [Fact p.Prime]
    {F A B : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    [CommRing A] [IsDomain A] [CommRing B]
    (χ : MulChar F A) (hχ : χ ≠ 1) {ζ : A} (hζ : ζ ^ p = 1)
    (red : A →+* B) (ι : F →+* B)
    (hred : ∀ x : F, red (χ x) = ι x⁻¹)
    (hsq : (red ζ - 1) ^ 2 = 0) :
    red (integralTraceGaussSum χ hζ) = -(red ζ - 1) := by
  classical
  have hval (x : F) :
      ((Algebra.trace (ZMod p) F x).val : B) =
        ι (algebraMap (ZMod p) F (Algebra.trace (ZMod p) F x)) := by
    have h := ZMod.natCast_zmod_val (Algebra.trace (ZMod p) F x)
    calc
      _ = ι (algebraMap (ZMod p) F ((Algebra.trace (ZMod p) F x).val : ZMod p)) := by rw [map_natCast, map_natCast]
      _ = _ := by rw [h]
  change red (∑ x : F, χ x * ζ ^ (Algebra.trace (ZMod p) F x).val) = _
  simp only [map_sum, map_mul, map_pow,
    pow_eq_one_add_of_sub_one_sq_zero (red ζ) hsq, mul_add, mul_one,
    Finset.sum_add_distrib]
  rw [← map_sum, MulChar.sum_eq_zero_of_ne_one hχ, map_zero, zero_add]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hred, hval, ← map_mul]
  rw [← map_sum, sum_inv_mul_trace, map_neg, map_one, neg_one_mul]


/-- The base Gauss congruence modulo the square of an ideal, from explicit
residue-field reduction data. -/
theorem integralTraceGaussSum_add_uniformizer_mem_sq {p : ℕ} [Fact p.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    [CommRing A] [IsDomain A]
    (χ : MulChar F A) (hχ : χ ≠ 1) {ζ : A} (hζ : ζ ^ p = 1)
    (I : Ideal A) (ι : F →+* A ⧸ I ^ 2)
    (hred : ∀ x : F, Ideal.Quotient.mk (I ^ 2) (χ x) = ι x⁻¹)
    (hmem : ζ - 1 ∈ I) :
    integralTraceGaussSum χ hζ + (ζ - 1) ∈ I ^ 2 := by
  have hsq : (Ideal.Quotient.mk (I ^ 2) ζ - 1) ^ 2 = 0 := by
    rw [← map_one (Ideal.Quotient.mk (I ^ 2)), ← map_sub, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hmem 2)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_add, map_sub, map_one,
    integralTraceGaussSum_first_order χ hχ hζ (Ideal.Quotient.mk (I ^ 2)) ι hred hsq,
    neg_add_cancel]

/-- Once the cyclotomic uniformizer has valuation one, the explicit Gauss
congruence proves that the first Gauss sum also has ideal valuation one. -/
theorem integralTraceGaussSum_emultiplicity_one {p : ℕ} [Fact p.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    [CommRing A] [IsDedekindDomain A]
    (χ : MulChar F A) (hχ : χ ≠ 1) {ζ : A} (hζ : ζ ^ p = 1)
    (I : Ideal A) (ι : F →+* A ⧸ I ^ 2)
    (hred : ∀ x : F, Ideal.Quotient.mk (I ^ 2) (χ x) = ι x⁻¹)
    (hmem : ζ - 1 ∈ I) (hnot : ζ - 1 ∉ I ^ 2) :
    emultiplicity I (Ideal.span {integralTraceGaussSum χ hζ}) = 1 := by
  have hc := integralTraceGaussSum_add_uniformizer_mem_sq χ hχ hζ I ι hred hmem
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, emultiplicity_eq_coe]
  constructor
  · rw [pow_one, Ideal.dvd_span_singleton]
    have hc' : integralTraceGaussSum χ hζ + (ζ - 1) ∈ I :=
      Ideal.pow_le_self (by decide : 2 ≠ 0) hc
    simpa only [add_sub_cancel_right] using I.sub_mem hc' hmem
  · rw [show 1 + 1 = 2 by rfl, Ideal.dvd_span_singleton]
    intro hg
    exact hnot (by simpa only [add_sub_cancel_left] using (I ^ 2).sub_mem hc hg)

end Catalan.Stickelberger
