import Catalan.CaseOne.ProductAnn

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M]

lemma submodule_cyclic_of_semisimple
    (hcyc : ∃ v : M, Function.Surjective (LinearMap.toSpanSingleton R M v))
    (P : Submodule R M) :
    ∃ v : P, Function.Surjective (LinearMap.toSpanSingleton R P v) := by
  obtain ⟨v, hv⟩ := hcyc
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  let proj : M →ₗ[R] P := P.projectionOnto Q hPQ
  let w : P := proj v
  refine ⟨w, ?_⟩
  have hproj : Function.Surjective proj := P.projectionOnto_surjective hPQ
  intro x
  obtain ⟨m, hm⟩ := hproj x
  obtain ⟨r, hr⟩ := hv m
  refine ⟨r, ?_⟩
  change r • proj v = x
  change r • v = m at hr
  rw [← proj.map_smul, hr, hm]

lemma annihilator_quotient_sup_of_cyclic_semisimple
    (hcyc : ∃ v : M, Function.Surjective (LinearMap.toSpanSingleton R M v))
    (P : Submodule R M) :
    Module.annihilator R (M ⧸ P) ⊔ Module.annihilator R P = ⊤ := by
  obtain ⟨v, hv⟩ := hcyc
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  let qeq : (M ⧸ P) ≃ₗ[R] Q := P.quotientEquivOfIsCompl Q hPQ
  let e : ((M ⧸ P) × P) ≃ₗ[R] M :=
    (qeq.prodCongr (LinearEquiv.refl R P)).trans
      ((LinearEquiv.prodComm R Q P).trans (P.prodEquivOfIsCompl Q hPQ))
  have hprod : ∃ w : (M ⧸ P) × P,
      Function.Surjective (LinearMap.toSpanSingleton R ((M ⧸ P) × P) w) := by
    refine ⟨e.symm v, ?_⟩
    intro x
    obtain ⟨r, hr⟩ := hv (e x)
    refine ⟨r, ?_⟩
    change r • e.symm v = x
    change r • v = e x at hr
    rw [← e.symm.map_smul, hr, e.symm_apply_apply]
  exact annihilator_sup_eq_top_of_cyclic_prod hprod

lemma annihilator_eq_mul_quotient_of_cyclic_semisimple
    (hcyc : ∃ v : M, Function.Surjective (LinearMap.toSpanSingleton R M v))
    (P : Submodule R M) :
    Module.annihilator R M = Module.annihilator R (M ⧸ P) * Module.annihilator R P := by
  obtain ⟨v, hv⟩ := hcyc
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  let qeq : (M ⧸ P) ≃ₗ[R] Q := P.quotientEquivOfIsCompl Q hPQ
  let e : ((M ⧸ P) × P) ≃ₗ[R] M :=
    (qeq.prodCongr (LinearEquiv.refl R P)).trans
      ((LinearEquiv.prodComm R Q P).trans (P.prodEquivOfIsCompl Q hPQ))
  have hprod : ∃ w : (M ⧸ P) × P,
      Function.Surjective (LinearMap.toSpanSingleton R ((M ⧸ P) × P) w) := by
    refine ⟨e.symm v, ?_⟩
    intro x
    obtain ⟨r, hr⟩ := hv (e x)
    refine ⟨r, ?_⟩
    change r • e.symm v = x
    change r • v = e x at hr
    rw [← e.symm.map_smul, hr, e.symm_apply_apply]
  rw [← e.annihilator_eq]
  exact annihilator_prod_eq_mul_of_cyclic_prod hprod

end Catalan.UnitReduction
