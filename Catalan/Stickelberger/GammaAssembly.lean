module

public import Catalan.Stickelberger.ThetaIdentity
public import Catalan.Stickelberger.Away
public import Catalan.IdealAction.Composition

/-! From a Gauss-power ideal factorization and a descended quotient to Θ_k principality. -/
/-!
# `Catalan.Stickelberger.GammaAssembly`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma theta_principal_of_gauss_quotient
    (J : FracIdealUnit K) (a : (ZMod p)ˣ) (Γ δ : Kˣ)
    (hΓ : ipow p K J (pθ p K) = principalIdeal K Γ)
    (hδ : δ ^ p = Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ) :
    ipow p K J (ΘS p K (a : ZMod p).val) = principalIdeal K δ := by
  apply principalIdeal_of_pow_eq K _ δ p hp.out.ne_zero
  have hpower : (ipow p K J (ΘS p K (a : ZMod p).val)) ^ p =
      principalIdeal K (Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ) := by
    rw [← zpow_natCast, ← ipow_zsmul, ← theta_identity, ipow_sub,
      ipow_zsmul, ipow_mul_single, hΓ, idealAct_principalIdeal]
    simp only [zpow_natCast, map_div, map_pow]
  rw [hδ]
  exact hpower

end Catalan
