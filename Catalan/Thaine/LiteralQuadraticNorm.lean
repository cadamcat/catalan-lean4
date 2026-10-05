module

public import Catalan.Thaine.LiteralMaps
public import Catalan.CaseOne.GaloisRing

/-!
# `Catalan.Thaine.LiteralQuadraticNorm`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance quadraticNormCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

private lemma quadratic_auxiliary_primitive
    (p : ℕ) [Fact p.Prime] : IsPrimitiveRoot (auxiliaryRoot p p) p := by
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
  exact A3.primitiveRoot_spec p (Fact.out : p.Prime).pos

private lemma quadratic_iota_auxiliary
    (p : ℕ) [Fact p.Prime] :
    ι p (A3.Bsub p p) (auxiliaryRoot p p) = (auxiliaryRoot p p)⁻¹ := by
  have hp : p.Prime := Fact.out
  have quadraticRootNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  have hroot := quadratic_auxiliary_primitive p
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p (A3.Bsub p p)
    (ι p (A3.Bsub p p)) hroot.pow_eq_one
  have hval : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
    simp only [Units.val_neg, Units.val_one, ZMod.val_neg_of_ne_zero, ZMod.val_one]
  simp only [ι, σ, MulEquiv.apply_symm_apply, hval] at h
  calc
    ι p (A3.Bsub p p) (auxiliaryRoot p p) = auxiliaryRoot p p ^ (p - 1) := h
    _ = (auxiliaryRoot p p)⁻¹ := by
      apply mul_right_cancel₀ (hroot.ne_zero hp.ne_zero)
      rw [inv_mul_cancel₀ (hroot.ne_zero hp.ne_zero), ← pow_succ,
        Nat.sub_add_cancel hp.one_le, hroot.pow_eq_one]

lemma literal_full_real_finrank
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Module.finrank (A3.F p) (A3.Bsub p p) = 2 := by
  have hp : p.Prime := Fact.out
  have quadraticFinrankNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  have hfull : Module.finrank ℚ (A3.Bsub p p) = p - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank p, Nat.totient_prime hp]
  have hreal := A3.finrank_F p hp hp2
  have hpos : 0 < Module.finrank ℚ (A3.F p) := Module.finrank_pos
  have htower := Module.finrank_mul_finrank ℚ (A3.F p) (A3.Bsub p p)
  rw [hreal, hfull] at htower
  rw [hreal] at hpos
  have heven : (p - 1) / 2 * 2 = p - 1 := by
    obtain ⟨r, hr⟩ := hp.even_sub_one hp2
    omega
  exact mul_left_cancel₀ hpos.ne' (htower.trans heven.symm)

lemma literal_iota_fixes_real
    (p : ℕ) [Fact p.Prime] (x : A3.F p) :
    ι p (A3.Bsub p p) (algebraMap (A3.F p) (A3.Bsub p p) x) =
      algebraMap (A3.F p) (A3.Bsub p p) x := by
  let i : A3.F p →ₐ[ℚ] A3.Bsub p p := IsScalarTower.toAlgHom ℚ (A3.F p) (A3.Bsub p p)
  have heq : (ι p (A3.Bsub p p)).toAlgHom.comp i = i := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    obtain rfl : z = A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹ := by simpa using hz
    change ι p (A3.Bsub p p) (auxiliaryRoot p p + (auxiliaryRoot p p)⁻¹) =
      auxiliaryRoot p p + (auxiliaryRoot p p)⁻¹
    rw [map_add, map_inv₀, quadratic_iota_auxiliary, inv_inv, add_comm]
  exact DFunLike.congr_fun heq x

private def quadraticRelativeIota (p : ℕ) [Fact p.Prime] :
    A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p :=
  AlgEquiv.ofRingEquiv (f := (ι p (A3.Bsub p p)).toRingEquiv) (literal_iota_fixes_real p)

private lemma quadraticRelativeIota_ne_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : quadraticRelativeIota p ≠ 1 := by
  intro heq
  have hp : p.Prime := Fact.out
  have hroot := quadratic_auxiliary_primitive p
  have hfix : ι p (A3.Bsub p p) (auxiliaryRoot p p) = auxiliaryRoot p p :=
    congrArg (fun tau : A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p => tau (auxiliaryRoot p p)) heq
  have hinv : auxiliaryRoot p p = (auxiliaryRoot p p)⁻¹ :=
    hfix.symm.trans (quadratic_iota_auxiliary p)
  have hpow : auxiliaryRoot p p ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [hinv]
    exact inv_mul_cancel₀ (hroot.ne_zero hp.ne_zero)
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) (hroot.dvd_of_pow_eq_one 2 hpow)
  exact hp2 (Nat.le_antisymm hle hp.two_le)

lemma literal_norm_eq_mul_iota
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x : A3.Bsub p p) :
    algebraMap (A3.F p) (A3.Bsub p p) (Algebra.norm (A3.F p) x) =
      x * ι p (A3.Bsub p p) x := by
  classical
  have quadraticNormRelativeGalois : IsGalois (A3.F p) (A3.Bsub p p) :=
    A3.isGalois_Bsub p p (Fact.out : p.Prime).pos
  let tau := quadraticRelativeIota p
  have htau : tau ≠ 1 := quadraticRelativeIota_ne_one p hp2
  have hcard : Nat.card (A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, literal_full_real_finrank p hp2]
  obtain ⟨rho, _, huniq⟩ := (Nat.card_eq_two_iff'
    (1 : A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p)).mp hcard
  have hcases (g : A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p) : g = 1 ∨ g = tau := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((huniq g hg).trans (huniq tau htau).symm)
  have huniv : (Finset.univ : Finset (A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p)) = {1, tau} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcases g
  rw [Algebra.norm_eq_prod_automorphisms, huniv,
    Finset.prod_insert (by simpa only [Finset.mem_singleton] using htau.symm), Finset.prod_singleton]
  rfl

end Catalan.Thaine
