module

public import Catalan.Stickelberger.TowerLift
public import Catalan.Stickelberger.Identify
public import Catalan.Stickelberger.Values
public import Catalan.FactorDescent

/-!
# `Catalan.Stickelberger.ConjugateValuation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Stickelberger
open NumberField

 theorem emultiplicity_conjIdeal_eq_orbit_sum_of_gaussFamily
    (p ell f m N : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L]
    [IsCyclotomicExtension {p} ℚ K] [IsCyclotomicExtension {N} ℚ L]
    (q : Ideal (𝓞 K)) [q.IsMaximal] [q.LiesOver (Ideal.span {(ell : ℤ)})]
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver (Ideal.span {(ell : ℤ)})] [P.LiesOver q]
    (hell : 2 < ell) (hne : ell ≠ p) (hf : 0 < f)
    (hm : m = ell ^ f - 1) (hN : N = ell * m) (hpm : p ∣ m)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 K)) (hχp : χ ^ p = 1)
    (τ : MulChar F (𝓞 L))
    (hχτ : χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L)) = τ ^ (m / p))
    {z : 𝓞 L} (hz : IsPrimitiveRoot z ell)
    (hval : ∀ a : ℕ, a < ell ^ f - 1 →
      emultiplicity P (Ideal.span {gaussFamily τ hz.pow_eq_one a}) = ((ell.digits a).sum : ℕ∞))
    (γ : 𝓞 K) (hγ0 : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 L) γ =
      (integralTraceGaussSum (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))) hz.pow_eq_one) ^ p)
    (b : (ZMod p)ˣ) :
    emultiplicity (Catalan.conjIdeal p K q b) (Ideal.span {γ}) =
      ((∑ i ∈ Finset.range f, ((b : ZMod p).val * ell ^ i) % p : ℕ) : ℕ∞) := by
  classical
  have hmpos : 0 < m := by
    have := Nat.le_self_pow hf.ne' ell
    omega
  have instLocal1 : NeZero m := ⟨hmpos.ne'⟩
  have hcop : ell.Coprime m :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : ell.Prime)).mpr
      (not_dvd_of_eq_pow_sub_one hell hf hm)
  have hzL : IsPrimitiveRoot (z : L) ell :=
    hz.map_of_injective (RingOfIntegers.coe_injective)
  obtain ⟨s, hsz, hs⟩ :=
    Catalan.exists_cyclotomic_tower_lift p ell m N K L hN hcop hpm hzL b
  let e := Catalan.integerAut K (Catalan.σ p K b)
  let sO := RingOfIntegers.mapRingEquiv s
  have hsOz : sO z = z := by
    apply RingOfIntegers.ext
    exact hsz
  have hsO (x : 𝓞 K) :
      sO (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) (e x) := by
    apply RingOfIntegers.ext
    exact hs (x : K)
  have hχs : (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))).ringHomComp sO.toRingHom =
      (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))) ^ (b : ZMod p).val := by
    ext1 u
    simp only [MulChar.ringHomComp_apply, MulChar.pow_apply_coe]
    change sO (algebraMap (𝓞 K) (𝓞 L) (χ (u : F))) =
      (algebraMap (𝓞 K) (𝓞 L) (χ (u : F))) ^ (b : ZMod p).val
    rw [hsO, ← map_pow]
    congr 1
    apply RingOfIntegers.ext
    have hxu : (χ (u : F)) ^ p = 1 := by
      simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using
        congrArg (fun ψ : MulChar F (𝓞 K) => ψ (u : F)) hχp
    have hxK : (χ (u : F) : K) ^ p = 1 := by
      exact_mod_cast hxu
    change Catalan.σ p K b (χ (u : F) : K) = (χ (u : F) : K) ^ (b : ZMod p).val
    simpa only [Catalan.σ, MulEquiv.apply_symm_apply] using
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p K
        (Catalan.σ p K b) hxK
  have hγimage : algebraMap (𝓞 K) (𝓞 L) (e γ) =
      gaussFamily τ hz.pow_eq_one (m / p * (b : ZMod p).val) ^ p := by
    have hn := integralTraceGaussSum_ringHom_of_fixed_root
      (χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))) hz.pow_eq_one sO.toRingHom hsOz
    change sO (integralTraceGaussSum _ hz.pow_eq_one) = _ at hn
    rw [← hsO, hγ, map_pow, hn, hχs, hχτ, ← pow_mul]
    rfl
  have hq0 : q ≠ ⊥ := by
    intro hq
    have hmemb := natCast_mem_of_liesOver ell K q
    rw [hq, Ideal.mem_bot] at hmemb
    exact (Fact.out : ell.Prime).ne_zero (by exact_mod_cast hmemb)
  have hP0 : P ≠ ⊥ := by
    intro hP
    have hmemb := natCast_mem_of_liesOver ell L P
    rw [hP, Ideal.mem_bot] at hmemb
    exact (Fact.out : ell.Prime).ne_zero (by exact_mod_cast hmemb)
  have hdm : m / p * p = ell ^ f - 1 := (Nat.div_mul_cancel hpm).trans hm
  have hdpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hmpos hpm)
    (Fact.out : p.Prime).pos
  have hb : (b : ZMod p).val < p := ZMod.val_lt _
  have hindex : m / p * (b : ZMod p).val < ell ^ f - 1 := by
    rw [← hdm]
    exact Nat.mul_lt_mul_of_pos_left hb hdpos
  have hspan : (Ideal.span {e γ} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hγ0 (e.injective (h.trans (map_zero e).symm))
  have hup : emultiplicity P
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) (Ideal.span {e γ})) =
      ((p * (ell.digits (m / p * (b : ZMod p).val)).sum : ℕ) : ℕ∞) := by
    rw [Ideal.map_span, Set.image_singleton, hγimage, ← Ideal.span_singleton_pow,
      emultiplicity_pow (Ideal.prime_of_isPrime hP0 inferInstance), hval _ hindex,
      Nat.cast_mul]
  have hdown := emultiplicity_eq_orbit_sum q P (Ideal.map_ne_bot_of_ne_bot hq0)
    ell p f (m / p) (b : ZMod p).val (by omega) (Fact.out : p.Prime).one_lt hf
    hdm hb (ramificationIdx_tower_eq ell p f m N K L q P hell hne hf hm hN)
    (e γ) hspan hup
  have hinv : (Catalan.integerAut K (Catalan.σ p K b)⁻¹) (e γ) = γ := by
    apply RingOfIntegers.ext
    exact (Catalan.σ p K b).symm_apply_apply (γ : K)
  have htransport := emultiplicity_ideal_map_span
    (Catalan.integerAut K (Catalan.σ p K b)⁻¹) q (e γ)
  rw [hinv] at htransport
  exact htransport.trans hdown

end Catalan.Stickelberger

