module

public import Mathlib

/-!
# `Catalan.CaseOne.MinpolyCyclic`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma minpoly_eq_charpoly_of_polynomial_cyclic
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V)
    (h : ∃ v : Module.AEval' T, Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial F) (Module.AEval' T) v)) :
    minpoly F T = T.charpoly := by
  obtain ⟨v, hv⟩ := h
  let a := LinearMap.toSpanSingleton (Polynomial F) (Module.AEval' T) v
  have hker : LinearMap.ker a = Module.annihilator (Polynomial F) (Module.AEval' T) := by
    ext P
    rw [LinearMap.mem_ker, Module.mem_annihilator]
    change P • v = 0 ↔ ∀ w : Module.AEval' T, P • w = 0
    constructor
    · intro hPv w
      obtain ⟨Q, rfl⟩ := hv w
      change P • (Q • v) = 0
      rw [smul_comm P Q v, hPv, smul_zero]
    · intro hP
      exact hP v
  have hdim : Module.finrank F (Module.AEval' T) = (minpoly F T).natDegree := by
    let e := (a.quotKerEquivOfSurjective hv).restrictScalars F
    have he := e.finrank_eq
    rw [hker, ← Polynomial.span_minpoly_eq_annihilator F T,
      finrank_quotient_span_eq_natDegree] at he
    exact he.symm
  have hdimV : Module.finrank F V = (minpoly F T).natDegree :=
    (Module.AEval'.of T).finrank_eq.trans hdim
  have hdeg : T.charpoly.natDegree ≤ (minpoly F T).natDegree := by
    rw [LinearMap.charpoly_natDegree, hdimV]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (LinearMap.isIntegral T)) (LinearMap.charpoly_monic T)
    (LinearMap.minpoly_dvd_charpoly T) hdeg).symm

end Catalan.UnitReduction
