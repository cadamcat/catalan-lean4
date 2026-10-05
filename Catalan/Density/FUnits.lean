module

public import Catalan.CaseOne.RealUnits
public import Catalan.CaseOne.DualCharpoly
public import Catalan.CaseOne.ProjectiveRigidity
public import Catalan.Density.FStructure

/-!
# `Catalan.Density.FUnits`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]

lemma F_infinitePlace_card (hp2 : p ≠ 2) :
    Fintype.card (InfinitePlace (F p)) = (p - 1) / 2 := by
  have instRealF : IsTotallyReal (F p) := isTotallyReal_F p (Fact.out : p.Prime).pos
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank,
    finrank_F p Fact.out hp2]

lemma F_unit_charpoly (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (τ : G p (F p)) (hτ : ∀ σ : G p (F p), σ ∈ Subgroup.zpowers τ) :
    (UnitModule.unitRepresentation p (F p) q τ).charpoly =
      ∑ i ∈ Finset.range ((p - 1) / 2), (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  have instRealF : IsTotallyReal (F p) := isTotallyReal_F p (Fact.out : p.Prime).pos
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p (Fact.out : p.Prime).pos
  rw [UnitModule.real_unit_charpoly_of_generator p (F p) q
    ((Fact.out : q.Prime).odd_of_ne_two hq2) τ hτ, F_infinitePlace_card p hp2]

lemma F_unit_dual_charpoly (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (τ : G p (F p)) (hτ : ∀ σ : G p (F p), σ ∈ Subgroup.zpowers τ) :
    ((UnitModule.unitRepresentation p (F p) q).dual τ).charpoly =
      ∑ i ∈ Finset.range ((p - 1) / 2), (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  rw [UnitReduction.representation_dual_charpoly]
  apply F_unit_charpoly p q hp2 hq2 τ⁻¹
  simpa only [Subgroup.zpowers_inv] using hτ

lemma F_unit_dual_cyclic (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hdegree : ¬ q ∣ (p - 1) / 2) (τ : G p (F p))
    (hτ : ∀ σ : G p (F p), σ ∈ Subgroup.zpowers τ) :
    ∃ v : Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual τ),
      Function.Surjective (LinearMap.toSpanSingleton (Polynomial (ZMod q))
        (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual τ)) v) := by
  apply UnitReduction.exists_cyclic_vector_of_squarefree_charpoly
  rw [F_unit_dual_charpoly p q hp2 hq2 τ hτ]
  exact UnitReduction.geometricSum_squarefree q _ hdegree

lemma F_unit_dual_minpoly (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hdegree : ¬ q ∣ (p - 1) / 2) (τ : G p (F p))
    (hτ : ∀ σ : G p (F p), σ ∈ Subgroup.zpowers τ) :
    minpoly (ZMod q) ((UnitModule.unitRepresentation p (F p) q).dual τ) =
      ∑ i ∈ Finset.range ((p - 1) / 2), (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  rw [UnitReduction.minpoly_eq_charpoly_of_polynomial_cyclic _
    (F_unit_dual_cyclic p q hp2 hq2 hdegree τ hτ),
    F_unit_dual_charpoly p q hp2 hq2 τ hτ]

lemma F_unit_dual_projective_generator (hp7 : 7 ≤ p) (hq2 : q ≠ 2)
    (hdegree : ¬ q ∣ (p - 1) / 2) (τ : G p (F p))
    (hτ : ∀ σ : G p (F p), σ ∈ Subgroup.zpowers τ) :
    ∃ v : Module.Dual (ZMod q) (UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q),
      v ≠ 0 ∧ Function.Surjective
        (LinearMap.toSpanSingleton (Polynomial (ZMod q))
          (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual τ))
          (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual τ) v)) ∧
      ∀ (k : ℕ), k < (p - 1) / 2 → ∀ a : ZMod q,
        (((UnitModule.unitRepresentation p (F p) q).dual τ) ^ k) v = a • v →
          k = 0 ∧ a = 1 := by
  let T := (UnitModule.unitRepresentation p (F p) q).dual τ
  have hp2 : p ≠ 2 := by omega
  have hn : 2 < (p - 1) / 2 := by omega
  obtain ⟨w, hw⟩ := F_unit_dual_cyclic p q hp2 hq2 hdegree τ hτ
  let v := (Module.AEval'.of T).symm w
  have hv : Function.Surjective (LinearMap.toSpanSingleton (Polynomial (ZMod q))
      (Module.AEval' T) (Module.AEval'.of T v)) := by
    simpa only [v, LinearEquiv.apply_symm_apply] using hw
  have hr (k : ℕ) (hk : k < (p - 1) / 2) (a : ZMod q)
      (hscalar : (T ^ k) v = a • v) : k = 0 ∧ a = 1 :=
    UnitReduction.cyclic_geometric_projective_rigidity T _ hn
      (F_unit_dual_minpoly p q hp2 hq2 hdegree τ hτ) v hv k hk a hscalar
  refine ⟨v, ?_, hv, hr⟩
  intro hz
  have hbad := (hr 0 (by omega) 0 (by simp [hz])).2
  exact zero_ne_one hbad

end Catalan.A3
