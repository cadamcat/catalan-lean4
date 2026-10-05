module

public import Catalan.Density.ResidueRoot
public import Catalan.Density.ResiduePowerMap
public import Catalan.Density.IntegralUnitRoot
public import Catalan.Density.FixedResidue
public import Catalan.Density.GaloisModules
public import Catalan.Density.FiniteT

/-!
# `Catalan.Density.KummerResidue`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma kummerFunctional_zero_of_residue_power
    (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (ell : ℕ) (hell : ell.Prime) (hqell : q ≠ ell)
    (P : Ideal (𝓞 (T p q))) (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (hfrob : IsArithmeticFrob ell P (sigmaB.restrictScalars ℚ))
    (u : (𝓞 (F p))ˣ)
    (hres : ∃ v : (𝓞 (F p) ⧸ P.under (𝓞 (F p)))ˣ,
      v ^ q = Units.map (Ideal.Quotient.mk (P.under (𝓞 (F p)))).toMonoidHom u) :
    kummerFunctional p q (restrictTToM p q sigmaB) (UnitQuotient.powerClass q u) = 0 := by
  have instNumberFieldT : NumberField (T p q) := numberField_T p q hq
  have hqprime : q.Prime := Fact.out
  let uB : (𝓞 (Bsub p q))ˣ := Units.map
    (algebraMap (𝓞 (F p)) (𝓞 (Bsub p q))).toMonoidHom u
  let uT : (𝓞 (T p q))ˣ := Units.map
    (algebraMap (𝓞 (F p)) (𝓞 (T p q))).toMonoidHom u
  let r : T p q := algebraMap (Msub p q) (T p q) (unitRoot p q hqprime.pos u)
  have hr : r ^ q = ((uT : 𝓞 (T p q)) : T p q) := by
    change (algebraMap (Msub p q) (T p q) (unitRoot p q hqprime.pos u)) ^ q =
      algebraMap (F p) (T p q) ((u : 𝓞 (F p)) : F p)
    rw [← map_pow, unitRoot_pow]
    exact (IsScalarTower.algebraMap_apply (F p) (Msub p q) (T p q) _).symm
  obtain ⟨rO, hrOcoe, hrO⟩ := Kummer.exists_integralUnit_of_field_root
    (T p q) q hqprime.pos uT r hr
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
  have hcard : Nat.card (𝓞 (Bsub p q) ⧸ P.under (𝓞 (Bsub p q))) = ell :=
    card_quotient_under_of_arithmeticFrob_fixes (Bsub p q) (T p q) ell hell P
      (sigmaB.restrictScalars ℚ) hfrob (fun x => sigmaB.commutes x)
  have hrB : rO ^ q = Units.map
      (algebraMap (𝓞 (Bsub p q)) (𝓞 (T p q))).toMonoidHom uB := by
    rw [hrO]
    apply Units.ext
    change algebraMap (𝓞 (F p)) (𝓞 (T p q)) (u : 𝓞 (F p)) =
      algebraMap (𝓞 (Bsub p q)) (𝓞 (T p q))
        (algebraMap (𝓞 (F p)) (𝓞 (Bsub p q)) (u : 𝓞 (F p)))
    exact IsScalarTower.algebraMap_apply _ _ _ _
  have hresB := Kummer.residue_power_map_tower
    (𝓞 (F p)) (𝓞 (Bsub p q)) (𝓞 (T p q)) q P u hres
  have hfix := Kummer.integral_root_fixed_of_residue_power (Bsub p q) (T p q)
    q ell hqprime hell hqell P hfrob.1 hfrob.2.2.1 hcard sigmaB
    (fun x => hfrob.2.2.2.2.2.2 x) zetaO hzeta uB rO hrB hresB
  have hfixT : sigmaB r = r := by
    have h := congrArg (fun x : 𝓞 (T p q) => (x : T p q)) hfix
    change sigmaB ((rO : 𝓞 (T p q)) : T p q) = ((rO : 𝓞 (T p q)) : T p q) at h
    simpa only [hrOcoe] using h
  apply (kummerFunctional_apply_eq_zero_iff p q (restrictTToM p q sigmaB) u).mpr
  apply (kummerValue_eq_one_iff p q (restrictTToM p q sigmaB) u).mpr
  apply (algebraMap (Msub p q) (T p q)).injective
  rw [restrictTToM_commutes]
  exact hfixT

end Catalan.A3
