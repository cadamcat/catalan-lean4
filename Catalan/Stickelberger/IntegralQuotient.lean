module

public import Catalan.Stickelberger.TowerLift
public import Catalan.Stickelberger.GaussFamily

/-!
# `Catalan.Stickelberger.IntegralQuotient`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Stickelberger
open NumberField

 theorem exists_integralGaussSum_quotient_power
    (p ell m N : ℕ) [Fact p.Prime] [Fact ell.Prime] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L] [IsGalois K L]
    [IsCyclotomicExtension {p} ℚ K] [IsCyclotomicExtension {N} ℚ L]
    (hN : N = ell * m) (hcop : ell.Coprime m) (hpm : p ∣ m)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 K)) (hχp : χ ^ p = 1)
    {z : 𝓞 L} (hz : IsPrimitiveRoot z ell)
    (γ : 𝓞 K)
    (hγ : algebraMap (𝓞 K) (𝓞 L) γ =
      (integralTraceGaussSum (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))) hz.pow_eq_one) ^ p)
    (a : (ZMod p)ˣ) :
    ∃ δ : Kˣ, (δ : K) ^ p = (γ : K) ^ (a : ZMod p).val / Catalan.σ p K a (γ : K)
 := by
  have hell : ringChar F = ell := ringChar.eq F ell
  subst ell
  have instLocal1 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have instLocal2 : NeZero (ringChar F) := ⟨(Fact.out : (ringChar F).Prime).ne_zero⟩
  let χK : MulChar F K := χ.ringHomComp (algebraMap (𝓞 K) K)
  have hχK : χK ^ p = 1 := by
    simp only [χK, MulChar.ringHomComp_pow, hχp, MulChar.ringHomComp_one]
  have hzL : IsPrimitiveRoot (z : L) (ringChar F) :=
    hz.map_of_injective RingOfIntegers.coe_injective
  obtain ⟨s, hsz, hslift⟩ := Catalan.exists_cyclotomic_tower_lift
    p (ringChar F) m N K L hN hcop hpm hzL a
  have hsum : Catalan.traceGaussSum χK hzL.pow_eq_one =
      ((integralTraceGaussSum
        (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))) hz.pow_eq_one : 𝓞 L) : L) := by
    simp [Catalan.traceGaussSum, integralTraceGaussSum, gaussSum,
      Catalan.traceAddChar, χK, AddChar.zmodChar_apply, ← IsScalarTower.algebraMap_apply]
  have hγL : Catalan.traceGaussSum χK hzL.pow_eq_one ^ p =
      algebraMap K L (γ : K) := by
    rw [hsum]
    have h := congrArg (algebraMap (𝓞 L) L) hγ
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using h.symm
  obtain ⟨δ, _, hδ⟩ := Catalan.exists_traceGaussSum_quotient_power χK hχK
    (Catalan.ζ_spec p K) hzL (Catalan.σ p K a).toRingEquiv s
    (a : ZMod p).val (Catalan.σ_apply_ζ p K a) hsz hslift (γ : K) hγL
  exact ⟨δ, hδ⟩

end Catalan.Stickelberger

