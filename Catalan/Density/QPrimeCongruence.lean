module

public import Catalan.Density.RootResidueCard
public import Catalan.Density.IntegralUnitRoot
public import Catalan.Density.FixedResidue
public import Catalan.Density.GaloisModules
public import Catalan.Density.FiniteT

/-!
# `Catalan.Density.QPrimeCongruence`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma q_dvd_ell_sub_one_of_B_frobenius
    (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (ell : ℕ) (hell : ell.Prime) (hqell : q ≠ ell)
    (P : Ideal (𝓞 (T p q))) (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (hfrob : IsArithmeticFrob ell P (sigmaB.restrictScalars ℚ)) : q ∣ ell - 1 := by
  have instNumberFieldT : NumberField (T p q) := numberField_T p q hq
  have instMaxP : P.IsMaximal := hfrob.1
  have hqprime : q.Prime := Fact.out
  let PB : HeightOneSpectrum (𝓞 (Bsub p q)) :=
    ⟨P.under (𝓞 (Bsub p q)), inferInstance, Ideal.under_ne_bot (𝓞 (Bsub p q)) hfrob.2.1⟩
  have hcard : Nat.card (𝓞 (Bsub p q) ⧸ PB.asIdeal) = ell :=
    card_quotient_under_of_arithmeticFrob_fixes (Bsub p q) (T p q) ell hell P
      (sigmaB.restrictScalars ℚ) hfrob (fun x => sigmaB.commutes x)
  obtain ⟨zetaO, hzetaOcoe, _⟩ := Kummer.exists_integralUnit_of_field_root
    (Bsub p q) q hqprime.pos 1 (kummerZeta p q)
    (by simpa using (kummerZeta_spec p q hqprime.pos).pow_eq_one)
  have hzetaF : IsPrimitiveRoot
      (algebraMap (𝓞 (Bsub p q)) (Bsub p q) (zetaO : 𝓞 (Bsub p q))) q := by
    change IsPrimitiveRoot (((zetaO : 𝓞 (Bsub p q)) : Bsub p q)) q
    rw [hzetaOcoe]
    exact kummerZeta_spec p q hqprime.pos
  have hzeta : IsPrimitiveRoot (zetaO : 𝓞 (Bsub p q)) q :=
    hzetaF.of_map_of_injective RingOfIntegers.coe_injective
  exact Kummer.prime_dvd_residue_card_sub_one (Bsub p q) q ell hqprime hell hqell
    PB hcard zetaO hzeta

end Catalan.A3
