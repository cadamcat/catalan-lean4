module

public import Catalan.Density.KummerResidue
public import Catalan.Density.CyclicFunctional

/-!
# `Catalan.Density.UnitResidueInjective`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] kummerGalCommGroup kummerGalModule

private lemma functional_zero_of_nonzero_power
    (sigma : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q)
    (a : ℕ) (ha0 : 0 < a) (haq : a < q)
    (hz : kummerFunctional p q (sigma ^ a) z = 0) :
    kummerFunctional p q sigma z = 0 := by
  have hm := congrArg (fun f : Module.Dual (ZMod q)
      (UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q) => f z)
    ((kummerPairing p q).toAddMonoidHom.map_nsmul a (Additive.ofMul sigma))
  change kummerFunctional p q (sigma ^ a) z = a • kummerFunctional p q sigma z at hm
  have ha : (a : ZMod q) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt ha0 haq ((ZMod.natCast_eq_zero_iff a q).mp h)
  have hmzero : (a : ZMod q) * kummerFunctional p q sigma z = 0 := by
    simpa only [nsmul_eq_mul] using hm.symm.trans hz
  exact (mul_eq_zero.mp hmzero).resolve_left ha

lemma unit_qth_power_of_cyclic_prime_residues
    (hp : 0 < p) (hq : Odd q) (gamma : G p (F p))
    (tau : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (hcyc : Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial (ZMod q))
        (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual gamma))
        (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual gamma)
          (kummerFunctional p q tau))))
    (sigmaB : T p q ≃ₐ[Bsub p q] T p q) (rho : Msub p q ≃ₐ[ℚ] Msub p q)
    (hM : restrictTToM p q sigmaB = conjugateKummer p q hp rho tau)
    (ell : ℕ) (hell : ell.Prime) (hqell : q ≠ ell)
    (P : Ideal (𝓞 (T p q))) (a : ℕ) (ha0 : 0 < a) (haq : a < q)
    (hfrob : IsArithmeticFrob ell P ((sigmaB.restrictScalars ℚ) ^ a))
    (u : (𝓞 (F p))ˣ)
    (hres : ∀ g : G p (F p), ∃ v : (𝓞 (F p) ⧸ P.under (𝓞 (F p)))ˣ,
      v ^ q = Units.map (Ideal.Quotient.mk (P.under (𝓞 (F p)))).toMonoidHom
        (Circular.unitAction p (F p) g u)) :
    ∃ v : (𝓞 (F p))ˣ, v ^ q = u := by
  have hfrob' : IsArithmeticFrob ell P ((sigmaB ^ a).restrictScalars ℚ) := by
    have heq : (sigmaB ^ a).restrictScalars ℚ = (sigmaB.restrictScalars ℚ) ^ a :=
      (AlgEquiv.restrictScalarsHom ℚ).map_pow sigmaB a
    rw [heq]
    exact hfrob
  have hz : UnitQuotient.powerClass q u = 0 := by
    apply unit_class_eq_zero_of_conjugate_cyclic_functional p q hp gamma tau hcyc rho
    intro g
    change kummerFunctional p q (conjugateKummer p q hp rho tau)
      (UnitQuotient.powerMap q (Circular.unitAction p (F p) g) (UnitQuotient.powerClass q u)) = 0
    rw [UnitQuotient.powerMap_apply]
    have hg := kummerFunctional_zero_of_residue_power p q hq ell hell hqell P
      (sigmaB ^ a) hfrob' (Circular.unitAction p (F p) g u) (hres g)
    rw [map_pow] at hg
    have hg' := functional_zero_of_nonzero_power p q (restrictTToM p q sigmaB)
      (UnitQuotient.powerClass q (Circular.unitAction p (F p) g u)) a ha0 haq hg
    simpa only [hM] using hg'
  change (QuotientGroup.mk u : (𝓞 (F p))ˣ ⧸ UnitQuotient.qPowers (𝓞 (F p))ˣ q) = 1 at hz
  exact (QuotientGroup.eq_one_iff u).mp hz

end Catalan.A3
