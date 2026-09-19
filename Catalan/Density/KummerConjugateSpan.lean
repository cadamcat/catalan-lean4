import Catalan.Density.KummerCovariance

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
local instance conjugateSpanKummerComm : CommGroup (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
  kummerGalCommGroup p q
local instance conjugateSpanKummerModule :
    Module (ZMod q) (Additive (Msub p q ≃ₐ[Bsub p q] Msub p q)) :=
  kummerGalModule p q

lemma kummer_conjugates_span (hp : 0 < p) (gamma : G p (F p))
    (tau : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (hcyc : Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial (ZMod q))
        (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual gamma))
        (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual gamma)
          (kummerFunctional p q tau)))) :
    Submodule.span (ZMod q)
      (Set.range (fun sigma : Msub p q ≃ₐ[ℚ] Msub p q =>
        Additive.ofMul (conjugateKummer p q hp sigma tau))) = ⊤ := by
  let conjugateSpanAbsoluteGalois : IsGalois ℚ (Msub p q) :=
    isGalois_Msub_rat p q hp (Fact.out : q.Prime).pos
  let conjugateSpanBaseAbelian : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  let E := kummerDualEquiv p q
  let T := (UnitModule.unitRepresentation p (F p) q).dual gamma
  let v := kummerFunctional p q tau
  let W := Submodule.span (ZMod q)
    (Set.range (fun sigma : Msub p q ≃ₐ[ℚ] Msub p q =>
      Additive.ofMul (conjugateKummer p q hp sigma tau)))
  have hpowers (n : ℕ) : E.symm ((T ^ n) v) ∈ W := by
    obtain ⟨sigma, hsigma⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (E := Msub p q) (K₁ := F p) (gamma ^ n)
    have hrestrict : restrictToF p q hp sigma = gamma ^ n := hsigma
    have hcov : E (Additive.ofMul (conjugateKummer p q hp sigma tau)) =
        cyclotomicScalar p q sigma • ((T ^ n) v) := by
      change kummerFunctional p q (conjugateKummer p q hp sigma tau) = _
      rw [kummerFunctional_conjugate, hrestrict, map_pow]
    have hmem : E.symm (cyclotomicScalar p q sigma • ((T ^ n) v)) ∈ W := by
      rw [← hcov, E.symm_apply_apply]
      exact Submodule.subset_span (Set.mem_range_self sigma)
    have hscaled := W.smul_mem (cyclotomicScalar p q sigma)⁻¹ hmem
    simpa only [map_smul, smul_smul,
      inv_mul_cancel₀ (cyclotomicScalar_ne_zero p q sigma), one_smul] using hscaled
  have hpoly (P : Polynomial (ZMod q)) : E.symm ((Polynomial.aeval T P) v) ∈ W := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simpa only [map_add, LinearMap.add_apply] using W.add_mem hP hQ
    | monomial n a =>
      simpa only [Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul] using W.smul_mem a (hpowers n)
  apply top_unique
  intro z _
  change z ∈ W
  obtain ⟨P, hP⟩ := hcyc (Module.AEval'.of T (E z))
  rw [LinearMap.toSpanSingleton_apply] at hP
  have hback := congrArg (Module.AEval'.of T).symm hP
  have heval : (Polynomial.aeval T P) v = E z := by
    simpa only [T, v, Module.AEval.of_symm_smul, LinearEquiv.symm_apply_apply,
      Module.End.smul_def] using hback
  have hmem := hpoly P
  rw [heval, E.symm_apply_apply] at hmem
  exact hmem

end Catalan.A3
