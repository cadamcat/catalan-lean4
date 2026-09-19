import Catalan.Thaine.CircularClosure
import Catalan.Thaine.AuxiliaryIntegralHilbert90

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma exists_circular_hilbert90_data
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) :
    ∃ (eta : (𝓞 (A3.Bsub p ell))ˣ)
      (tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell) (alpha : 𝓞 (A3.Bsub p ell)),
      alpha ≠ 0 ∧
      tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val ∧
      orderOf tau = ell - 1 ∧
      (∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
        sigma ∈ Subgroup.zpowers tau) ∧
      A3.integralAut tau alpha = (eta : 𝓞 (A3.Bsub p ell)) * alpha ∧
      Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 ∧
      ∀ P : Ideal (𝓞 (A3.Bsub p ell)), P.IsMaximal → (ell : 𝓞 (A3.Bsub p ell)) ∈ P →
        (eta : 𝓞 (A3.Bsub p ell)) -
          algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) ∈ P := by
  obtain ⟨eta, hnorm, hres⟩ := auxiliary_norm_unit p ell hp2 hpe hell d hd
  obtain ⟨tau, htau, horder, hgen, alpha, halpha, heq⟩ :=
    auxiliary_integral_hilbert90 p ell hpe s hs eta hnorm
  exact ⟨eta, tau, alpha, halpha, htau, horder, hgen, heq, hnorm, hres⟩

end Catalan.Thaine
