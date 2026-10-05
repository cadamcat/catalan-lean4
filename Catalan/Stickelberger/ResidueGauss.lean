module

public import Catalan.Cyclotomic.Ramification
public import Catalan.Stickelberger.GaussCharacters

/-!
# `Catalan.Stickelberger.ResidueGauss`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Reduction of the fixed cyclotomic root at an ideal. -/
def residueZeta (I : Ideal (𝓞 K)) : 𝓞 K ⧸ I :=
  Ideal.Quotient.mk I (ζ_spec p K).toInteger

lemma residueZeta_isPrimitiveRoot (I : Ideal (𝓞 K)) [I.IsPrime]
    (haway : (p : 𝓞 K) ∉ I) : IsPrimitiveRoot (residueZeta p K I) p := by
  have hpow : residueZeta p K I ^ p = 1 := by
    rw [residueZeta, ← map_pow, (ζ_spec p K).toInteger_isPrimitiveRoot.pow_eq_one,
      map_one]
  have hne : residueZeta p K I ≠ 1 := by
    intro h
    apply haway
    apply I.mem_of_dvd (ζ_spec p K).toInteger_sub_one_dvd_prime'
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr h
  exact isPrimitiveRoot_of_mem_nthRootsFinset hp.out
    ((Polynomial.mem_nthRootsFinset hp.out.pos 1).mpr hpow) hne

/-- Every prime residue field away from p contains a primitive p-th root. -/
lemma prime_dvd_residue_card_sub_one (I : Ideal (𝓞 K))
    (hI : I.IsPrime) (hI0 : I ≠ ⊥) (haway : (p : 𝓞 K) ∉ I) :
    p ∣ Nat.card (𝓞 K ⧸ I) - 1 := by
  let : I.IsPrime := hI
  let : I.IsMaximal := hI.isMaximal hI0
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  have hroot := residueZeta_isPrimitiveRoot p K I haway
  simpa only [Fintype.card_eq_nat_card] using hroot.dvd_of_pow_eq_one
    (Fintype.card (𝓞 K ⧸ I) - 1)
    (FiniteField.pow_card_sub_one_eq_one (residueZeta p K I) (hroot.ne_zero hp.out.ne_zero))

/-- The trace Gauss sum for the actual ideal quotient, in K(ζ_ell).
The finite-field and prime-field algebra structures are supplied internally. -/
def primeResidueGaussSum (I : Ideal (𝓞 K)) [I.IsMaximal]
    (χ : MulChar (𝓞 K ⧸ I) K) : CyclotomicField (ringChar (𝓞 K ⧸ I)) K := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  let : Algebra (ZMod (ringChar (𝓞 K ⧸ I))) (𝓞 K ⧸ I) := ZMod.algebra _ _
  exact cyclotomicTraceGaussSum χ

/-- At an actual nonzero prime ideal away from p, there is a nonzero Gauss sum
of an exact-order p multiplicative character whose p-th power descends to K. -/
theorem exists_primeResidueGaussSum_descended_power (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) :
    ∃ χ : MulChar (𝓞 K ⧸ I) K, orderOf χ = p ∧
      primeResidueGaussSum K I χ ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K (CyclotomicField (ringChar (𝓞 K ⧸ I)) K) (Γ : K) =
        primeResidueGaussSum K I χ ^ p := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  let : Algebra (ZMod (ringChar (𝓞 K ⧸ I))) (𝓞 K ⧸ I) := ZMod.algebra _ _
  have hI0 : I ≠ ⊥ := (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
  have hcard : p ∣ Fintype.card (𝓞 K ⧸ I) - 1 := by
    simpa only [Fintype.card_eq_nat_card] using
      prime_dvd_residue_card_sub_one p K I inferInstance hI0 haway
  exact exists_cyclotomicTraceGaussSum_descended_power p hp.out.one_lt hcard (ζ_spec p K)

end Catalan

