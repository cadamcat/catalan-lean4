module

public import Catalan.CaseOne.GroupEvaluation

/-!
# `Catalan.CaseOne.RepresentationAnnihilator`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma representation_annihilator_eq_span_minpoly
    {k G V : Type*} [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (τ : G) (hτ : ∀ g : G, g ∈ Subgroup.zpowers τ) :
    Module.annihilator (MonoidAlgebra k G) ρ.asModule =
      Ideal.span {Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) (minpoly k (ρ τ))} := by
  have hann (a : MonoidAlgebra k G) :
      a ∈ Module.annihilator (MonoidAlgebra k G) ρ.asModule ↔ ρ.asAlgebraHom a = 0 := by
    rw [Module.mem_annihilator]
    constructor
    · intro ha
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := ρ.asModuleEquiv.surjective v
      rw [← Representation.asModuleEquiv_map_smul, ha w, map_zero]
      rfl
    · intro ha w
      apply ρ.asModuleEquiv.injective
      rw [Representation.asModuleEquiv_map_smul, ha, LinearMap.zero_apply, map_zero]
  have heval (P : Polynomial k) :
      ρ.asAlgebraHom (Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) P) =
        Polynomial.aeval (ρ τ) P := by
    simpa only [Representation.asAlgebraHom_single_one] using
      (Polynomial.aeval_algHom_apply ρ.asAlgebraHom (MonoidAlgebra.single τ (1 : k)) P).symm
  apply le_antisymm
  · intro a ha
    obtain ⟨P, rfl⟩ := cyclic_group_algebra_aeval_surjective k G τ hτ a
    have hzero := (hann _).mp ha
    rw [heval] at hzero
    obtain ⟨Q, hQ⟩ := minpoly.dvd k (ρ τ) hzero
    apply Submodule.mem_span_singleton.mpr
    refine ⟨Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) Q, ?_⟩
    change Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) Q *
      Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) (minpoly k (ρ τ)) =
        Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k)) P
    rw [← map_mul, hQ, mul_comm Q]
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    apply (hann _).mpr
    rw [heval, minpoly.aeval k (ρ τ)]

end Catalan.UnitReduction
