module

public import Catalan.CaseOne.LogSpaceEquiv

/-!
# `Catalan.CaseOne.PlaceCycle`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma exists_place_cycle_equiv (τ : K ≃ₐ[ℚ] K)
    (hτ : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers τ) (w : InfinitePlace K) :
    ∃ e : ZMod (Fintype.card (InfinitePlace K)) ≃ InfinitePlace K,
      e 0 = w ∧ ∀ i, e (i + 1) = (e i).comap τ.toRingEquiv.toRingHom := by
  classical
  have horbit (v : InfinitePlace K) : v ∈ MulAction.orbit (Subgroup.zpowers τ⁻¹) w := by
    have hbase : w.comap (algebraMap ℚ K) = v.comap (algebraMap ℚ K) :=
      Subsingleton.elim _ _
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq hbase
    refine ⟨⟨σ, ?_⟩, hσ⟩
    rw [Subgroup.zpowers_inv]
    exact hτ σ
  let orbitEquiv : MulAction.orbit (Subgroup.zpowers τ⁻¹) w ≃ InfinitePlace K :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v, horbit v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let instOrbitFintype : Fintype (MulAction.orbit (Subgroup.zpowers τ⁻¹) w) :=
    Fintype.ofFinite _
  have hperiod : Function.minimalPeriod (τ⁻¹ • ·) w = Fintype.card (InfinitePlace K) :=
    (MulAction.minimalPeriod_eq_card τ⁻¹ w).trans (Fintype.card_congr orbitEquiv)
  rw [← hperiod]
  let e : ZMod (Function.minimalPeriod (τ⁻¹ • ·) w) ≃ InfinitePlace K :=
    (MulAction.orbitZPowersEquiv τ⁻¹ w).symm.trans orbitEquiv
  have heint (k : ℤ) : e (k : ZMod (Function.minimalPeriod (τ⁻¹ • ·) w)) = τ⁻¹ ^ k • w := by
    change ((MulAction.orbitZPowersEquiv τ⁻¹ w).symm (k : ZMod (Function.minimalPeriod (τ⁻¹ • ·) w))).val = _
    rw [MulAction.orbitZPowersEquiv_symm_apply']
    rfl
  refine ⟨e, ?_, ?_⟩
  · simpa only [Int.cast_zero, zpow_zero, one_smul] using heint 0
  · intro i
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
    have hcast : (k : ZMod (Function.minimalPeriod (τ⁻¹ • ·) w)) + 1 =
        ((k + 1 : ℤ) : ZMod (Function.minimalPeriod (τ⁻¹ • ·) w)) := by simp
    rw [hcast, heint, heint]
    change τ⁻¹ ^ (k + 1) • w = τ⁻¹ • (τ⁻¹ ^ k • w)
    rw [add_comm k 1, zpow_add, zpow_one, mul_smul]

end Catalan.UnitLog
