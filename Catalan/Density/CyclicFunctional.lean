import Catalan.Density.KummerConjugateSpan

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] kummerGalCommGroup kummerGalModule

lemma unit_class_eq_zero_of_cyclic_functional (hp : 0 < p) (gamma : G p (F p))
    (tau : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (hcyc : Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial (ZMod q))
        (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual gamma))
        (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual gamma)
          (kummerFunctional p q tau))))
    (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q)
    (hz : ∀ g : G p (F p),
      kummerFunctional p q tau (UnitModule.unitRepresentation p (F p) q g z) = 0) :
    z = 0 := by
  let e : Additive (Msub p q ≃ₐ[Bsub p q] Msub p q) →ₗ[ZMod q] ZMod q :=
    (kummerPairing p q).flip z
  have hker : Submodule.span (ZMod q)
      (Set.range (fun rho : Msub p q ≃ₐ[ℚ] Msub p q =>
        Additive.ofMul (conjugateKummer p q hp rho tau))) ≤ LinearMap.ker e := by
    apply Submodule.span_le.mpr
    rintro _ ⟨rho, rfl⟩
    change kummerFunctional p q (conjugateKummer p q hp rho tau) z = 0
    rw [kummerFunctional_conjugate_apply, hz, mul_zero]
  rw [kummer_conjugates_span p q hp gamma tau hcyc] at hker
  apply kummerFunctional_right_nondegenerate p q z
  intro sigma
  exact hker (show Additive.ofMul sigma ∈ (⊤ : Submodule (ZMod q) _) from trivial)

lemma unit_class_eq_zero_of_conjugate_cyclic_functional (hp : 0 < p) (gamma : G p (F p))
    (tau : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (hcyc : Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial (ZMod q))
        (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual gamma))
        (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual gamma)
          (kummerFunctional p q tau))))
    (rho : Msub p q ≃ₐ[ℚ] Msub p q)
    (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q)
    (hz : ∀ g : G p (F p),
      kummerFunctional p q (conjugateKummer p q hp rho tau)
        (UnitModule.unitRepresentation p (F p) q g z) = 0) : z = 0 := by
  apply unit_class_eq_zero_of_cyclic_functional p q hp gamma tau hcyc z
  intro g
  have h := hz (restrictToF p q hp rho * g)
  rw [kummerFunctional_conjugate_apply] at h
  have he : UnitModule.unitRepresentation p (F p) q (restrictToF p q hp rho)⁻¹
      (UnitModule.unitRepresentation p (F p) q (restrictToF p q hp rho * g) z) =
        UnitModule.unitRepresentation p (F p) q g z := by
    change (UnitModule.unitRepresentation p (F p) q (restrictToF p q hp rho)⁻¹ *
      UnitModule.unitRepresentation p (F p) q (restrictToF p q hp rho * g)) z = _
    rw [← map_mul, inv_mul_cancel_left]
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left (cyclotomicScalar_ne_zero p q rho)

end Catalan.A3
