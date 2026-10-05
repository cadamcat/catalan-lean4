module

public import Mathlib

/-!
# `Catalan.CaseOne.CyclicVector`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

private def polynomialAction
    (F M : Type*) [Field F] [AddCommGroup M] [Module F M]
    [Module (Polynomial F) M] [IsScalarTower F (Polynomial F) M] : M →ₗ[F] M :=
  (Algebra.lsmul F F M : Polynomial F →ₐ[F] Module.End F M) Polynomial.X

private lemma aeval_polynomialAction
    (F M : Type*) [Field F] [AddCommGroup M] [Module F M]
    [Module (Polynomial F) M] [IsScalarTower F (Polynomial F) M] (P : Polynomial F) :
    Polynomial.aeval (polynomialAction F M) P =
      (Algebra.lsmul F F M : Polynomial F →ₐ[F] Module.End F M) P := by
  simpa only [polynomialAction, Polynomial.aeval_X_left_apply] using
    Polynomial.aeval_algHom_apply
      (Algebra.lsmul F F M : Polynomial F →ₐ[F] Module.End F M) Polynomial.X P

lemma exists_cyclic_vector_of_squarefree_charpoly
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (hT : Squarefree T.charpoly) :
    ∃ v : Module.AEval' T, Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial F) (Module.AEval' T) v) := by
  classical
  let M := Module.AEval' T
  have instSemisimpleM : IsSemisimpleModule (Polynomial F) M :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hT (LinearMap.aeval_self_charpoly T)
  obtain ⟨v, hv⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator (Polynomial F) M
  let a := LinearMap.toSpanSingleton (Polynomial F) M v
  let W : Submodule (Polynomial F) M := LinearMap.range a
  obtain ⟨U, hWU⟩ := exists_isCompl W
  have instFiniteW : FiniteDimensional F W :=
    FiniteDimensional.of_injective (W.subtype.restrictScalars F) Subtype.val_injective
  have instFiniteU : FiniteDimensional F U :=
    FiniteDimensional.of_injective (U.subtype.restrictScalars F) Subtype.val_injective
  let TW : W →ₗ[F] W := polynomialAction F W
  let TU : U →ₗ[F] U := polynomialAction F U
  let TM : M →ₗ[F] M := polynomialAction F M
  let e0 : V ≃ₗ[F] M := Module.AEval'.of T
  have hTM : e0.conj T = TM := by
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := e0.surjective m
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact (Module.AEval'.X_smul_of T x).symm
  have hTMchar : TM.charpoly = T.charpoly := by
    rw [← hTM, LinearEquiv.charpoly_conj]
  let ep : (W × U) ≃ₗ[Polynomial F] M := W.prodEquivOfIsCompl U hWU
  let e : (W × U) ≃ₗ[F] M := ep.restrictScalars F
  have hconj : e.conj (TW.prodMap TU) = TM := by
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := e.surjective m
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change ep ((Polynomial.X : Polynomial F) • x) = (Polynomial.X : Polynomial F) • ep x
    exact ep.map_smul (Polynomial.X : Polynomial F) x
  have hfac : T.charpoly = TW.charpoly * TU.charpoly := by
    rw [← hTMchar, ← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
  have hcop : IsRelPrime TW.charpoly TU.charpoly :=
    (squarefree_mul_iff.mp (hfac ▸ hT)).1
  have hvW : v ∈ W := ⟨1, by simp [a, LinearMap.toSpanSingleton_apply]⟩
  have hWv : TW.charpoly • (⟨v, hvW⟩ : W) = 0 := by
    have hz := LinearMap.congr_fun (LinearMap.aeval_self_charpoly TW) (⟨v, hvW⟩ : W)
    rw [aeval_polynomialAction] at hz
    exact hz
  have hker : TW.charpoly ∈ LinearMap.ker a := by
    change TW.charpoly • v = 0
    exact congrArg Subtype.val hWv
  have hann : TW.charpoly ∈ Module.annihilator (Polynomial F) M := by
    rw [← hv]
    exact hker
  have hUann : Polynomial.aeval TU TW.charpoly = 0 := by
    rw [aeval_polynomialAction]
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact Module.mem_annihilator.mp hann (u : M)
  have hminW : minpoly F TU ∣ TW.charpoly := minpoly.dvd F TU hUann
  have hminU : minpoly F TU ∣ TU.charpoly := LinearMap.minpoly_dvd_charpoly TU
  have hunit : IsUnit (minpoly F TU) := hcop hminW hminU
  have hzeroUnit : IsUnit (0 : Module.End F U) := by
    have hm := hunit.map (Polynomial.aeval TU)
    rwa [minpoly.aeval F TU] at hm
  have honezero : (1 : Module.End F U) = 0 := (isUnit_zero_iff.mp hzeroUnit).symm
  have hUbot : U = ⊥ := by
    apply bot_unique
    intro u hu
    have hz := LinearMap.congr_fun honezero (⟨u, hu⟩ : U)
    exact (Submodule.mem_bot (Polynomial F)).mpr (congrArg Subtype.val hz)
  have hWtop : W = ⊤ := by simpa only [hUbot, sup_bot_eq] using hWU.sup_eq_top
  exact ⟨v, LinearMap.range_eq_top.mp hWtop⟩

end Catalan.UnitReduction
