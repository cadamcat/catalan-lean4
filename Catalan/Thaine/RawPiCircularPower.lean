module

public import Catalan.CaseOne.CircularUnits
public import Catalan.Cyclotomic.GroupRing

/-!
# `Catalan.Thaine.RawPiCircularPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma raw_pi_circular_power
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (pi : Kˣ) (hpi : (pi : K) = 1 - ζ p K)
    (Theta : R p K) (hw : (q : ℤ) ∣ weight p K Theta) :
    ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧ ∃ b : Kˣ,
      upow p K pi Theta = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q := by
  classical
  have hp : p.Prime := Fact.out
  let j : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hratio (g : G p K) : ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧
      actUnit p K g pi = j c * pi := by
    obtain ⟨a, rfl⟩ := (σ_bijective p K).surjective g
    obtain ⟨c, hc⟩ := Circular.exists_ratio_unit p K a 1
    refine ⟨c, Subgroup.subset_closure (Or.inr ⟨a, 1, hc⟩), ?_⟩
    apply Units.ext
    change σ p K a (pi : K) = ((c : 𝓞 K) : K) * (pi : K)
    rw [hpi, map_sub, map_one, σ_apply_ζ, hc]
    simp only [Units.val_one, ZMod.val_one'' hp.ne_one, pow_one]
    exact (div_mul_cancel₀ _ (sub_ne_zero.mpr ((ζ_spec p K).ne_one hp.one_lt).symm)).symm
  have hfactor : ∀ Psi : R p K, ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧
      upow p K pi Psi = j c * pi ^ weight p K Psi := by
    intro Psi
    refine MonoidAlgebra.induction_linear Psi ?_ ?_ ?_
    · refine ⟨1, (Circular.circularUnits p K).one_mem, ?_⟩
      simp only [upow_zero, weight_zero, map_one, zpow_zero, mul_one]
    · intro A B hA hB
      obtain ⟨c, hc, hca⟩ := hA
      obtain ⟨d, hd, hdb⟩ := hB
      refine ⟨c * d, (Circular.circularUnits p K).mul_mem hc hd, ?_⟩
      rw [upow_add, hca, hdb, map_mul, weight_add, zpow_add]
      ac_rfl
    · intro g m
      obtain ⟨c, hc, hcg⟩ := hratio g
      refine ⟨c ^ m, (Circular.circularUnits p K).zpow_mem hc m, ?_⟩
      have hweight : weight p K (MonoidAlgebra.single g m) = m :=
        Finsupp.sum_single_index rfl
      rw [upow_single, hcg, hweight, map_zpow, mul_zpow]
  obtain ⟨c, hc, hdecomp⟩ := hfactor Theta
  obtain ⟨k, hk⟩ := hw
  refine ⟨c, hc, pi ^ k, ?_⟩
  rw [hdecomp, hk, mul_comm (q : ℤ) k, zpow_mul, zpow_natCast]

end Catalan.Thaine
