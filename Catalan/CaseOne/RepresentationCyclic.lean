import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma representation_cyclic_of_polynomial_cyclic
    {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (g : G)
    (h : ∃ v : Module.AEval' (ρ g), Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial k) (Module.AEval' (ρ g)) v)) :
    ∃ v : ρ.asModule, Function.Surjective
      (LinearMap.toSpanSingleton (MonoidAlgebra k G) ρ.asModule v) := by
  obtain ⟨v, hv⟩ := h
  let e := Module.AEval'.of (ρ g)
  refine ⟨ρ.asModuleEquiv.symm (e.symm v), ?_⟩
  intro w
  obtain ⟨P, hP⟩ := hv (e (ρ.asModuleEquiv w))
  refine ⟨Polynomial.aeval (MonoidAlgebra.single g (1 : k)) P, ?_⟩
  have hEval : ρ.asAlgebraHom (Polynomial.aeval (MonoidAlgebra.single g (1 : k)) P) =
      Polynomial.aeval (ρ g) P := by
    simpa only [Representation.asAlgebraHom_single_one] using
      (Polynomial.aeval_algHom_apply ρ.asAlgebraHom (MonoidAlgebra.single g (1 : k)) P).symm
  apply ρ.asModuleEquiv.injective
  rw [LinearMap.toSpanSingleton_apply, Representation.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply, hEval]
  rw [LinearMap.toSpanSingleton_apply] at hP
  have hback := congrArg e.symm hP
  simpa only [e, Module.AEval.of_symm_smul, LinearEquiv.symm_apply_apply, Module.End.smul_def]
    using hback

end Catalan.UnitReduction
