module

public import Mathlib

/-!
# `Catalan.Thaine.Hilbert90`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma hilbert90_cyclic {F L : Type*} [Field F] [Field L] [Algebra F L]
    (tau : L ≃ₐ[F] L) (d : ℕ) (hd : 0 < d) (ho : orderOf tau = d)
    (eta : Lˣ)
    (hN : (∏ i ∈ Finset.range d,
      Units.map (tau ^ i).toRingEquiv.toRingHom.toMonoidHom eta) = 1) :
    ∃ alpha : Lˣ,
      Units.map tau.toRingEquiv.toRingHom.toMonoidHom alpha / alpha = eta := by
  classical
  let b : ℕ → L := fun n => ∏ i ∈ Finset.range n, (tau ^ i) (eta : L)
  let c : ℕ → L := fun n => (b n)⁻¹
  have hb0 : b 0 = 1 := by simp [b]
  have hbd : b d = 1 := by
    have h := congrArg (fun u : Lˣ => (u : L)) hN
    simpa [b] using h
  have hb_step (i : ℕ) : b (i + 1) = tau (b i) * (eta : L) := by
    dsimp [b]
    rw [Finset.prod_range_succ']
    simp only [map_prod, pow_zero, AlgEquiv.one_apply]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [pow_succ', AlgEquiv.mul_apply]
  have hc0 : c 0 = 1 := by simp [c, hb0]
  have hcd : c d = 1 := by simp [c, hbd]
  have hc_step (i : ℕ) : tau (c i) = (eta : L) * c (i + 1) := by
    dsimp [c]
    rw [map_inv₀, hb_step]
    field_simp
  have hpow : tau ^ d = 1 := by rw [← ho, pow_orderOf_eq_one]
  have hLI : LinearIndependent L (fun i : Fin d => (fun x : L => (tau ^ i.val) x)) := by
    apply (linearIndependent_monoidHom L L).comp
      (fun i : Fin d => (tau ^ i.val).toRingEquiv.toRingHom.toMonoidHom)
    intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := tau)
      (by change i.val < orderOf tau; rw [ho]; exact i.isLt)
      (by change j.val < orderOf tau; rw [ho]; exact j.isLt)
    ext x
    exact congrArg (fun f : L →* L => f x) hij
  obtain ⟨x, hx⟩ : ∃ x : L, (∑ i ∈ Finset.range d, c i * (tau ^ i) x) ≠ 0 := by
    by_contra! h
    have hzero : (∑ i : Fin d, c i.val • (fun x : L => (tau ^ i.val) x)) = 0 := by
      ext x
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        (Fin.sum_univ_eq_sum_range (fun i => c i * (tau ^ i) x) d).trans (h x)
    have hc := (Fintype.linearIndependent_iff.mp hLI) (fun i : Fin d => c i.val) hzero
      ⟨0, hd⟩
    simp [hc0] at hc
  let a : L := ∑ i ∈ Finset.range d, c i * (tau ^ i) x
  have ha : a ≠ 0 := hx
  have hshift : (∑ i ∈ Finset.range d, c (i + 1) * (tau ^ (i + 1)) x) = a := by
    have hs := (Finset.sum_range_succ (fun i => c i * (tau ^ i) x) d).symm.trans
      (Finset.sum_range_succ' (fun i => c i * (tau ^ i) x) d)
    simp only [hc0, hcd, hpow, pow_zero, AlgEquiv.one_apply, one_mul] at hs
    exact (add_right_cancel hs).symm
  have hta : tau a = (eta : L) * a := by
    dsimp [a]
    simp only [map_sum, map_mul, hc_step]
    simp_rw [← AlgEquiv.mul_apply, ← pow_succ']
    simp only [mul_assoc, ← Finset.mul_sum]
    exact congrArg ((eta : L) * ·) hshift
  refine ⟨Units.mk0 a ha, ?_⟩
  apply Units.ext
  simpa using (div_eq_iff ha).mpr hta

end Catalan.Thaine
