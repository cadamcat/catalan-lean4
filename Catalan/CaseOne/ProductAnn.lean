import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma annihilator_sup_eq_top_of_cyclic_prod
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hcyc : ∃ v : M × N, Function.Surjective (LinearMap.toSpanSingleton R (M × N) v)) :
    Module.annihilator R M ⊔ Module.annihilator R N = ⊤ := by
  obtain ⟨v, hsurj⟩ := hcyc
  rcases v with ⟨vM, vN⟩
  obtain ⟨a, ha⟩ := hsurj (vM, 0)
  obtain ⟨b, hb⟩ := hsurj (0, vN)
  change a • (vM, vN) = (vM, 0) at ha
  change b • (vM, vN) = (0, vN) at hb
  have haM : a • vM = vM := congrArg Prod.fst ha
  have haN : a • vN = 0 := congrArg Prod.snd ha
  have hbM : b • vM = 0 := congrArg Prod.fst hb
  have hbN : b • vN = vN := congrArg Prod.snd hb
  have hleft : (1 - a : R) ∈ Module.annihilator R M := by
    apply Module.mem_annihilator.mpr
    intro m
    obtain ⟨c, hc⟩ := hsurj (m, 0)
    change c • (vM, vN) = (m, 0) at hc
    have hcm : c • vM = m := congrArg Prod.fst hc
    have hzero : (1 - a : R) • vM = 0 := by
      rw [sub_smul, one_smul, haM, sub_self]
    rw [← hcm, smul_smul, mul_comm, ← smul_smul, hzero, smul_zero]
  have hright : a ∈ Module.annihilator R N := by
    apply Module.mem_annihilator.mpr
    intro n
    obtain ⟨c, hc⟩ := hsurj (0, n)
    change c • (vM, vN) = (0, n) at hc
    have hcn : c • vN = n := congrArg Prod.snd hc
    have hzero : a • vN = 0 := haN
    rw [← hcn, smul_smul, mul_comm, ← smul_smul, hzero, smul_zero]
  apply (Ideal.eq_top_iff_one _).mpr
  have h1 : (1 - a : R) ∈ Module.annihilator R M ⊔ Module.annihilator R N :=
    Submodule.mem_sup_left hleft
  have h2 : a ∈ Module.annihilator R M ⊔ Module.annihilator R N :=
    Submodule.mem_sup_right (show a ∈ Module.annihilator R N from hright)
  convert Submodule.add_mem _ h1 h2 using 1 <;> ring

lemma annihilator_prod_eq_mul_of_cyclic_prod
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hcyc : ∃ v : M × N, Function.Surjective (LinearMap.toSpanSingleton R (M × N) v)) :
    Module.annihilator R (M × N) = Module.annihilator R M * Module.annihilator R N := by
  have hsup : Module.annihilator R M ⊔ Module.annihilator R N = ⊤ :=
    annihilator_sup_eq_top_of_cyclic_prod hcyc
  rw [Module.annihilator_prod]
  exact (Ideal.mul_eq_inf_of_coprime hsup).symm

end Catalan.UnitReduction
