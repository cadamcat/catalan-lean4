import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma cyclic_geometric_projective_rigidity
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : V →ₗ[F] V) (n : ℕ) (hn : 2 < n)
    (hmin : minpoly F T = ∑ i ∈ Finset.range n, (Polynomial.X : Polynomial F) ^ i)
    (v : V) (hcyc : Function.Surjective
      (LinearMap.toSpanSingleton (Polynomial F) (Module.AEval' T) (Module.AEval'.of T v)))
    (k : ℕ) (hk : k < n) (a : F) (hscalar : (T ^ k) v = a • v) :
    k = 0 ∧ a = 1 := by
  classical
  let P : Polynomial F := Polynomial.X ^ k - Polynomial.C a
  let S : Polynomial F := ∑ i ∈ Finset.range n, (Polynomial.X : Polynomial F) ^ i
  have hPv : P • Module.AEval'.of T v = 0 := by
    rw [show P = Polynomial.X ^ k - Polynomial.C a from rfl, sub_smul,
      Module.AEval'.X_pow_smul_of, Module.AEval.C_smul]
    change Module.AEval'.of T ((T ^ k) v) - a • Module.AEval'.of T v = 0
    rw [hscalar, map_smul, sub_self]
  have hzero : Polynomial.aeval T P = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨Q, hQ⟩ := hcyc (Module.AEval'.of T w)
    rw [LinearMap.toSpanSingleton_apply] at hQ
    have hPw : P • Module.AEval'.of T w = 0 := by
      rw [← hQ, smul_comm P Q _, hPv, smul_zero]
    have hh := congrArg (Module.AEval'.of T).symm hPw
    simpa only [Module.AEval.of_symm_smul, LinearEquiv.symm_apply_apply, map_zero,
      Module.End.smul_def, LinearMap.zero_apply] using hh
  have hdiv : S ∣ P := by
    change (∑ i ∈ Finset.range n, (Polynomial.X : Polynomial F) ^ i) ∣ P
    rw [← hmin]
    exact minpoly.dvd F T hzero
  have hcoeff (j : ℕ) : S.coeff j = if j < n then 1 else 0 := by
    simp [S, Polynomial.coeff_X_pow]
  have hdegS : S.natDegree = n - 1 := by
    apply le_antisymm
    · dsimp only [S]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [Polynomial.natDegree_X_pow]
      have hi' := Finset.mem_range.mp hi
      omega
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hcoeff, if_pos (by omega : n - 1 < n)]
      exact one_ne_zero
  have hmonicS : S.Monic := by
    change S.coeff S.natDegree = 1
    rw [hdegS, hcoeff, if_pos (by omega : n - 1 < n)]
  by_cases hP : P = 0
  · have hk0 : k = 0 := by
      by_contra hk0
      exact Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk0) a hP
    refine ⟨hk0, ?_⟩
    have he := congrArg (fun Q : Polynomial F => Q.coeff 0) hP
    have ha0 : (1 : F) - a = 0 := by simpa [P, hk0] using he
    exact (sub_eq_zero.mp ha0).symm
  · exfalso
    have hdegP : P.natDegree = k := Polynomial.natDegree_X_pow_sub_C
    have hle : n - 1 ≤ k := by
      rw [← hdegS, ← hdegP]
      exact Polynomial.natDegree_le_of_dvd hdiv hP
    have hkn : k = n - 1 := by omega
    have hkpos : 0 < k := by omega
    have hmonicP : P.Monic := Polynomial.monic_X_pow_sub_C a hkpos.ne'
    have heq : P = S := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      hmonicS hmonicP hdiv (by rw [hdegP, hdegS, hkn])
    have hp1 : P.coeff 1 = 0 := by
      have h1k : 1 ≠ k := by omega
      simp [P, Polynomial.coeff_X_pow, h1k]
    have hs1 : S.coeff 1 = 1 := by rw [hcoeff, if_pos (by omega : 1 < n)]
    have hc := congrArg (fun Q : Polynomial F => Q.coeff 1) heq
    rw [hp1, hs1] at hc
    exact zero_ne_one hc

end Catalan.UnitReduction
