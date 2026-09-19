import Catalan.CaseOne.CircularUnits
import Catalan.CaseOne.PrimaryNaturality

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Circular
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma circularUnits_stable (τ : G p K) (u : (𝓞 K)ˣ)
    (hu : u ∈ circularUnits p K) : unitAction p K τ u ∈ circularUnits p K := by
  have hle : circularUnits p K ≤ (circularUnits p K).comap (unitAction p K τ) := by
    apply (Subgroup.closure_le _).mpr
    intro v hv
    change unitAction p K τ v ∈ circularUnits p K
    apply Subgroup.subset_closure
    rcases hv with hv | ⟨a, b, hv⟩
    · left
      change IsOfFinOrder (unitAction p K τ v)
      obtain ⟨n, hn, hvn⟩ := isOfFinOrder_iff_pow_eq_one.mp (show IsOfFinOrder v from hv)
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      rw [← map_pow, hvn, map_one]
    · obtain ⟨g, rfl⟩ := (σ_bijective p K).surjective τ
      refine Or.inr ⟨g * a, g * b, ?_⟩
      have hindex (c : (ZMod p)ˣ) :
          σ p K g (ζ p K ^ (c : ZMod p).val) = ζ p K ^ ((g * c : (ZMod p)ˣ) : ZMod p).val := by
        rw [← σ_apply_ζ p K c, ← σ_apply_ζ p K (g * c), σ_mul]
        rfl
      rw [unitAction_coe, hv, map_div₀, map_sub, map_one, map_sub, map_one,
        hindex, hindex]
  exact hle hu

lemma primaryCircularUnits_stable (q : ℕ) (hq : 0 < q) (τ : G p K) (u : (𝓞 K)ˣ)
    (hu : u ∈ primaryCircularUnits p K q) :
    unitAction p K τ u ∈ primaryCircularUnits p K q := by
  refine ⟨circularUnits_stable p K τ u hu.1, ?_⟩
  exact UnitQuotient.primaryUnits_map (𝓞 K) (𝓞 K) q hq
    (RingOfIntegers.mapRingHom τ.toRingEquiv.toRingHom) u hu.2

end Catalan.Circular

