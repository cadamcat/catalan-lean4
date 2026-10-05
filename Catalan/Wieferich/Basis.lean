module

public import Catalan.Wieferich.Defs
public import Mathlib

/-!
# `Catalan.Wieferich.Basis`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Module
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private lemma inverseConjugate_eq_power (a : (ZMod p)ˣ) :
    inverseConjugate p K a = (zetaInteger p K) ^ (((-a⁻¹ : (ZMod p)ˣ) : ZMod p).val) := by
  have hinv : σ p K (a⁻¹) = (σ p K a)⁻¹ :=
    (IsCyclotomicExtension.Rat.galEquivZMod p K).symm.map_inv a
  apply RingOfIntegers.ext
  change (σ p K a)⁻¹ ((ζ p K) ^ (p - 1)) =
    (ζ p K) ^ (((-a⁻¹ : (ZMod p)ˣ) : ZMod p).val)
  rw [map_pow, ← hinv, σ_apply_ζ, ← pow_mul]
  apply pow_eq_pow_of_modEq _ (ζ_spec p K).pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    Nat.cast_sub (Fact.out : p.Prime).one_le, ZMod.natCast_self, Nat.cast_one]
  simp only [zero_sub, mul_neg_one, Units.val_neg]

lemma inverseConjugates_basis :
    ∃ B : Basis (ZMod p)ˣ ℤ (𝓞 K),
      ∀ a, B a = inverseConjugate p K a := by
  classical
  let pb := (ζ_spec p K).integralPowerBasis
  have hdim : pb.dim = p - 1 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime (Fact.out : p.Prime)]
  have hgen : pb.gen = zetaInteger p K :=
    IsPrimitiveRoot.integralPowerBasis_gen (ζ_spec p K)
  let j : (ZMod p)ˣ → ℕ := fun a => (((-a⁻¹ : (ZMod p)ˣ) : ZMod p).val)
  have hjpos (a : (ZMod p)ˣ) : 0 < j a := ZMod.val_pos.mpr (Units.ne_zero _)
  have hjlt (a : (ZMod p)ˣ) : j a < p := ZMod.val_lt _
  let idx : (ZMod p)ˣ → Fin pb.dim := fun a =>
    ⟨j a - 1, by rw [hdim]; have := hjpos a; have := hjlt a; omega⟩
  have hinj : Function.Injective idx := by
    intro a b h
    have hh := congrArg Fin.val h
    change j a - 1 = j b - 1 at hh
    have hval : j a = j b := by have := hjpos a; have := hjpos b; omega
    have hu : (-a⁻¹ : (ZMod p)ˣ) = -b⁻¹ := Units.ext (ZMod.val_injective p hval)
    exact inv_injective (neg_injective hu)
  have hcard : Fintype.card (ZMod p)ˣ = Fintype.card (Fin pb.dim) := by
    rw [ZMod.card_units, Fintype.card_fin, hdim]
  let e : (ZMod p)ˣ ≃ Fin pb.dim :=
    Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).mpr ⟨hinj, hcard⟩)
  have hzunit : IsUnit (zetaInteger p K) :=
    (ζ_spec p K).toInteger_isPrimitiveRoot.isUnit (Fact.out : p.Prime).ne_zero
  let u : (𝓞 K)ˣ := hzunit.unit
  have hu : (u : 𝓞 K) = zetaInteger p K := hzunit.unit_spec
  refine ⟨(pb.basis.map (u.mulLeftLinearEquiv ℤ (𝓞 K))).reindex e.symm, ?_⟩
  intro a
  rw [Basis.reindex_apply, Basis.map_apply, Units.mulLeftLinearEquiv_apply,
    pb.basis_eq_pow]
  change (u : 𝓞 K) * pb.gen ^ (j a - 1) = inverseConjugate p K a
  rw [hu, hgen, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (hjpos a).ne')]
  exact (inverseConjugate_eq_power p K a).symm

lemma inverseConjugates_dvd_coeff (n : ℤ) (c : (ZMod p)ˣ → ℤ)
    (hd : (n : 𝓞 K) ∣
      ∑ a : (ZMod p)ˣ, (c a : 𝓞 K) * inverseConjugate p K a) :
    ∀ a, n ∣ c a := by
  classical
  obtain ⟨B, hB⟩ := inverseConjugates_basis p K
  obtain ⟨d, hd⟩ := hd
  have he : (∑ a : (ZMod p)ˣ, c a • B a) = n • d := by
    simpa only [hB, zsmul_eq_mul] using hd
  intro a
  refine ⟨B.repr d a, ?_⟩
  have hcoord := congrArg (fun t : 𝓞 K => B.repr t a) he
  simpa only [B.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] using hcoord

end Catalan.A1e

