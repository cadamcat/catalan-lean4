module

public import Catalan.Wieferich.Defs
public import Mathlib

/-!
# `Catalan.Wieferich.Frobenius`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma cyclotomic_frobenius_lift
    (q : ℕ) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ F : (𝓞 K) ≃+* (𝓞 K),
      ∀ a : 𝓞 K, (q : 𝓞 K) ∣ a ^ q - F a := by
  let pNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let qPrime : Fact q.Prime := ⟨hq⟩
  have hqp : q.Coprime p := ((Nat.coprime_primes (Fact.out : p.Prime) hq).mpr hpq).symm
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime q hqp
  let F : (𝓞 K) ≃+* (𝓞 K) := RingOfIntegers.mapRingEquiv (σ p K u).toRingEquiv
  have hFroot : F (ζ_spec p K).toInteger = (ζ_spec p K).toInteger ^ q := by
    apply RingOfIntegers.coe_injective
    change σ p K u (ζ p K) = ζ p K ^ q
    rw [σ_apply_ζ]
    simp only [u, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact (pow_eq_pow_mod q (ζ_spec p K).pow_eq_one).symm
  let I : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  let Q := (𝓞 K) ⧸ I
  let π : (𝓞 K) →+* Q := Ideal.Quotient.mk I
  have hmap : ∀ a : 𝓞 K, π (a ^ q) = π (F a) := by
    rcases subsingleton_or_nontrivial Q with hQ | hQ
    · intro a
      exact hQ.elim _ _
    · let quotientNontrivial : Nontrivial Q := hQ
      have hqzero : (q : Q) = 0 := by
        change π (q : 𝓞 K) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      let quotientChar : CharP Q q := (CharP.charP_iff_prime_eq_zero hq).mpr hqzero
      have heq : ((frobenius Q q).comp π).toIntAlgHom =
          (π.comp F.toRingHom).toIntAlgHom := by
        apply (ζ_spec p K).integralPowerBasis.algHom_ext
        change π ((ζ_spec p K).integralPowerBasis.gen) ^ q =
          π (F ((ζ_spec p K).integralPowerBasis.gen))
        rw [IsPrimitiveRoot.integralPowerBasis_gen, hFroot, map_pow]
      intro a
      have h := DFunLike.congr_fun heq a
      simpa only [RingHom.toIntAlgHom_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        frobenius_def, map_pow] using h
  refine ⟨F, fun a => ?_⟩
  apply Ideal.mem_span_singleton.mp
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hmap a)

end Catalan.A1e

