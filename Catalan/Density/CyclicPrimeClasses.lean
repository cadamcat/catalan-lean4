import Catalan.Density.CyclicSelectorFamily
import Catalan.Density.SelectorPrimes
import Catalan.Density.ClassGroupLinear
import Catalan.Density.HRestriction

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
attribute [local instance] TGalCommGroup TGalModule HGalCommGroup HGalModule
  kummerGalCommGroup kummerGalModule

def cyclicPrimeClasses (hq : Odd q) (tau : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (S : Finset ℕ) : Set (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q) :=
  {c | ∃ (sigmaB : T p q ≃ₐ[Bsub p q] T p q) (rho : Msub p q ≃ₐ[ℚ] Msub p q)
      (ell : ℕ) (P : Ideal (𝓞 (T p q))) (a : ℕ) (v : HeightOneSpectrum (𝓞 (F p))),
    Selector p q (sigmaB.restrictScalars ℚ) ∧
    restrictTToM p q sigmaB = conjugateKummer p q (Fact.out : p.Prime).pos rho tau ∧
    ell.Prime ∧ ell ∉ S ∧ ell ≠ p ∧ ell ≠ q ∧ 0 < a ∧ a < q ∧
    IsArithmeticFrob ell P ((sigmaB.restrictScalars ℚ) ^ a) ∧
    v.asIdeal = P.under (𝓞 (F p)) ∧ Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell ∧
    Subgroup.zpowers
      (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) =
        Subgroup.zpowers (restrictTToH p q sigmaB) ∧
    c = UnitQuotient.powerClass q (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))}

omit [Fact p.Prime] [Fact q.Prime] in
private lemma cyclic_prime_span_image_top
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A : Set M) (hA : Submodule.span R A = ⊤) :
    Submodule.span R (f '' A) = ⊤ := by
  rw [← Submodule.map_span, hA, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

omit [Fact p.Prime] [Fact q.Prime] in
private lemma additive_mem_of_mem_zpowers
    {R G : Type*} [Ring R] [CommGroup G] [Module R (Additive G)]
    (W : Submodule R (Additive G)) {g h : G}
    (hh : Additive.ofMul h ∈ W) (hg : g ∈ Subgroup.zpowers h) :
    Additive.ofMul g ∈ W := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact W.toAddSubgroup.zsmul_mem hh i

lemma exists_cyclic_prime_class_generators
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (hq : Odd q) (S : Finset ℕ) :
    ∃ (gamma : G p (F p)) (tau : Msub p q ≃ₐ[Bsub p q] Msub p q),
      (∀ g : G p (F p), g ∈ Subgroup.zpowers gamma) ∧ tau ≠ 1 ∧
      Function.Surjective
        (LinearMap.toSpanSingleton (Polynomial (ZMod q))
          (Module.AEval' ((UnitModule.unitRepresentation p (F p) q).dual gamma))
          (Module.AEval'.of ((UnitModule.unitRepresentation p (F p) q).dual gamma)
            (kummerFunctional p q tau))) ∧
      Submodule.span (ZMod q) (cyclicPrimeClasses p q hq tau S) = ⊤ := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨gamma, tau, hgamma, htau, hcyc, hfamily⟩ :=
    exists_cyclic_selector_family p q hp7 hq2 hdegree
  refine ⟨gamma, tau, hgamma, htau, hcyc, ?_⟩
  let A : Set (Additive (T p q ≃ₐ[Bsub p q] T p q)) :=
    {s | Selector p q ((Additive.toMul s).restrictScalars ℚ) ∧
      ∃ rho : Msub p q ≃ₐ[ℚ] Msub p q,
        restrictTToM p q (Additive.toMul s) = conjugateKummer p q hp rho tau}
  have hA : Submodule.span (ZMod q) A = ⊤ := hfamily
  let E := classGroupModQLinearEquivHGal p q hq
  let f : Additive (T p q ≃ₐ[Bsub p q] T p q) →ₗ[ZMod q]
      UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q :=
    E.symm.toLinearMap.comp (TToHLinear p q)
  have hf : Function.Surjective f :=
    E.symm.surjective.comp (TToHLinear_surjective p q hq)
  have himage : Submodule.span (ZMod q) (f '' A) = ⊤ :=
    cyclic_prime_span_image_top f hf A hA
  let W := Submodule.span (ZMod q) (cyclicPrimeClasses p q hq tau S)
  change W = ⊤
  apply top_unique
  rw [← himage]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hSel, rho, hrM⟩ := hs
  let sigmaB : T p q ≃ₐ[Bsub p q] T p q := Additive.toMul s
  obtain ⟨ell, hell, havoid, P, a, v, ha0, haq, hfrob, hv, hnorm, hcycle⟩ :=
    exists_prime_class_of_selector_avoiding p q hp hq sigmaB hSel (insert p (insert q S))
  have havoid' : ell ≠ p ∧ ell ≠ q ∧ ell ∉ S := by
    simpa only [Finset.mem_insert, not_or] using havoid
  let c : UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q :=
    UnitQuotient.powerClass q (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))
  have hc : c ∈ cyclicPrimeClasses p q hq tau S := by
    exact ⟨sigmaB, rho, ell, P, a, v, hSel, hrM, hell, havoid'.2.2,
      havoid'.1, havoid'.2.1, ha0, haq, hfrob, hv, hnorm, hcycle, rfl⟩
  have hcW : c ∈ W := Submodule.subset_span hc
  have hEc : E c = Additive.ofMul
      (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) :=
    classGroupModQLinearEquivHGal_powerClass p q hq _
  have hbase : Additive.ofMul
      (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) ∈
      W.comap E.symm.toLinearMap := by
    change E.symm (Additive.ofMul
      (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v)))) ∈ W
    rw [← hEc, E.symm_apply_apply]
    exact hcW
  have hmem : restrictTToH p q sigmaB ∈
      Subgroup.zpowers (classGroupToHGal p q hq
        (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) := by
    rw [hcycle]
    exact Subgroup.mem_zpowers _
  have hresult := additive_mem_of_mem_zpowers (W.comap E.symm.toLinearMap) hbase hmem
  exact hresult

end Catalan.A3
