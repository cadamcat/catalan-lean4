import Catalan.Density.GaloisModules
import Catalan.Density.SelectorLift
import Catalan.Density.TConjugate
import Catalan.Density.KummerConjugateSpan
import Catalan.Density.CyclicKummerCentralizer

set_option autoImplicit false
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] TGalCommGroup TGalModule kummerGalCommGroup kummerGalModule

def selectorVectors : Set (Additive (T p q ≃ₐ[Bsub p q] T p q)) :=
  {s | Selector p q ((Additive.toMul s).restrictScalars ℚ)}

lemma selectors_span [Fact p.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) :
    Submodule.span (ZMod q) (selectorVectors p q) = ⊤ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨gamma, tau, _, htau, _, hcyc, hcentral⟩ :=
    exists_cyclic_kummer_centralizer_element p q hp7 hq2 hdegree
  let S : Set (Additive (Msub p q ≃ₐ[Bsub p q] Msub p q)) :=
    Set.range (fun rho : Msub p q ≃ₐ[ℚ] Msub p q =>
      Additive.ofMul (conjugateKummer p q hp rho tau))
  have hS : Submodule.span (ZMod q) S = ⊤ :=
    kummer_conjugates_span p q hp gamma tau hcyc
  have hnonempty : S.Nonempty := Set.range_nonempty _
  have hrange : S ⊆ LinearMap.range (TToMLinear p q) := by
    rw [LinearMap.range_eq_top.mpr (TToMLinear_surjective p q)]
    exact Set.subset_univ S
  have hpre : Submodule.span (ZMod q) ((TToMLinear p q) ⁻¹' S) = ⊤ := by
    rw [Submodule.span_preimage_eq hnonempty hrange, hS, Submodule.comap_top]
  apply top_unique
  rw [← hpre]
  apply Submodule.span_mono
  intro s hs
  obtain ⟨rhoM, hrhoM⟩ := hs
  let sigma : T p q ≃ₐ[Bsub p q] T p q := Additive.toMul s
  have hrM : restrictTToM p q sigma = conjugateKummer p q hp rhoM tau := by
    exact (congrArg Additive.toMul hrhoM).symm
  obtain ⟨rho, hrho⟩ := restrictAbsoluteTToM_surjective p q hp rhoM
  let sigma0 := conjugateT p q hp rho⁻¹ sigma
  have hzero : restrictTToM p q sigma0 = tau := by
    dsimp only [sigma0]
    rw [restrictTToM_conjugate, map_inv, hrho, hrM, conjugateKummer_inv_cancel]
  have hsigma0 : Selector p q (sigma0.restrictScalars ℚ) := by
    apply selector_of_T_lift p q hp tau htau (fun r hr => (hcentral r hr).1) sigma0
    intro x
    rw [← restrictTToM_commutes, hzero]
  have hconj := selector_conjugateT p q hp rho sigma0 hsigma0
  have hback : conjugateT p q hp rho sigma0 = sigma :=
    conjugateT_inv_cancel p q hp rho sigma
  rw [hback] at hconj
  exact hconj

end Catalan.A3
