module

public import Catalan.Density.TTower
public import Catalan.Density.AbsoluteB

/-!
# `Catalan.Density.SelectorConjugate`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma selector_conjugate (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (sigma rho : T p q ≃ₐ[ℚ] T p q) (hsigma : Selector p q sigma) :
    Selector p q (rho * sigma * rho⁻¹) := by
  have instGaloisB : IsGalois ℚ (Bsub p q) := isGalois_Bsub_rat p q hp hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    let b : Bsub p q := ⟨(x : Omega), hx⟩
    have hb : algebraMap (Bsub p q) (T p q) b = x := by
      apply Subtype.ext
      exact algebraMap_Bsub_T_coe p q b
    have hpre : ((rho⁻¹ x : T p q) : Omega) ∈ Bsub p q := by
      rw [← hb, ← (rho⁻¹).restrictNormal_commutes (Bsub p q) b,
        algebraMap_Bsub_T_coe]
      exact ((rho⁻¹).restrictNormal (Bsub p q) b).property
    change rho (sigma (rho⁻¹ x)) = x
    rw [hsigma.fixesBase _ hpre]
    exact rho.apply_symm_apply x
  · intro hzero
    apply hsigma.ne_one
    have h := congrArg (fun s => rho⁻¹ * s * rho) hzero
    simpa [mul_assoc] using h
  · rw [conj_pow, hsigma.pow_eq_one, mul_one, mul_inv_cancel]
  · intro tau hcomm
    have hc : (rho⁻¹ * tau * rho) * sigma = sigma * (rho⁻¹ * tau * rho) := by
      have h := congrArg (fun s => rho⁻¹ * s * rho) hcomm
      simpa [mul_assoc] using h
    have ht := hsigma.centralizer_exponent (rho⁻¹ * tau * rho) hc
    have hpow : (rho⁻¹ * tau * rho) ^ q = rho⁻¹ * tau ^ q * rho := by
      simpa only [inv_inv] using (conj_pow (i := q) (a := rho⁻¹) (b := tau))
    rw [hpow] at ht
    have h := congrArg (fun s => rho * s * rho⁻¹) ht
    simpa [mul_assoc] using h

end Catalan.A3
