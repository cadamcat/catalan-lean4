module

public import Catalan.Thaine.AuxiliaryGenerator
public import Catalan.Density.FStructure

/-!
# `Catalan.Thaine.MixedDescent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

def mixedExtension (p ell : ℕ) : IntermediateField (A3.Bsub p ell) A3.Omega :=
  IntermediateField.adjoin (A3.Bsub p ell) {A3.primitiveRoot p}

def mixedPRoot (p ell : ℕ) : mixedExtension p ell :=
  ⟨A3.primitiveRoot p, IntermediateField.subset_adjoin (A3.Bsub p ell) _ (by simp)⟩

def mixedEllRoot (p ell : ℕ) : mixedExtension p ell :=
  algebraMap (A3.Bsub p ell) (mixedExtension p ell) (auxiliaryRoot p ell)

noncomputable instance mixedExtensionFiniteDimensional (p ell : ℕ) :
    FiniteDimensional (A3.Bsub p ell) (mixedExtension p ell) := by
  have instMixedFiniteAlgebraic : Algebra.IsAlgebraic ℚ A3.Omega := AlgebraicClosure.isAlgebraic ℚ
  exact IntermediateField.adjoin.finiteDimensional
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A3.primitiveRoot p)).isIntegral.tower_top)

noncomputable instance mixedExtensionNumberField (p ell : ℕ) :
    NumberField (mixedExtension p ell) := NumberField.of_module_finite (A3.Bsub p ell) (mixedExtension p ell)

lemma mixedExtension_isCyclotomic (p ell : ℕ) (hp : 0 < p) :
    IsCyclotomicExtension {p} (A3.Bsub p ell) (mixedExtension p ell) := by
  have instMixedCycloNeP : NeZero p := ⟨hp.ne'⟩
  have instMixedCycloAlgebraicRat : Algebra.IsAlgebraic ℚ A3.Omega := AlgebraicClosure.isAlgebraic ℚ
  have instMixedCycloAlgebraicB : Algebra.IsAlgebraic (A3.Bsub p ell) A3.Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (A3.Bsub p ell)
  exact (A3.primitiveRoot_spec p hp).intermediateField_adjoin_isCyclotomicExtension (A3.Bsub p ell)

private lemma mixed_ambient_action
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (s : (ZMod ell)ˣ) :
    ∃ sigma : A3.Omega ≃ₐ[ℚ] A3.Omega,
      sigma (A3.primitiveRoot p) = A3.primitiveRoot p ∧
      sigma (A3.primitiveRoot ell) = A3.primitiveRoot ell ^ (s : ZMod ell).val := by
  have instMixedAmbientNeP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have instMixedAmbientNeEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  have instMixedAmbientNeMul : NeZero (p * ell) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne ell)⟩
  have instMixedAmbientAlgebraic : Algebra.IsAlgebraic ℚ A3.Omega := AlgebraicClosure.isAlgebraic ℚ
  have instMixedAmbientAlgClosure : IsAlgClosure ℚ A3.Omega := ⟨inferInstance, instMixedAmbientAlgebraic⟩
  have instMixedAmbientNormal : Normal ℚ A3.Omega := IsAlgClosure.normal ℚ A3.Omega
  let Cp : IntermediateField ℚ A3.Omega := IntermediateField.adjoin ℚ {A3.primitiveRoot p}
  let Ce : IntermediateField ℚ A3.Omega := IntermediateField.adjoin ℚ {A3.primitiveRoot ell}
  let M : IntermediateField ℚ A3.Omega := Cp ⊔ Ce
  have hcop : p.Coprime ell := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ell.Prime)).mpr hpe
  have instMixedAmbientCycloM : IsCyclotomicExtension {p * ell} ℚ M := by
    let instMixedAmbientAlgebraCp : Algebra ℚ Cp := IntermediateField.algebra' Cp
    let instMixedAmbientAlgebraCe : Algebra ℚ Ce := IntermediateField.algebra' Ce
    let instMixedAmbientAlgebraM : Algebra ℚ M := IntermediateField.algebra' M
    have instMixedAmbientCycloP : IsCyclotomicExtension {p} ℚ Cp :=
      (A3.primitiveRoot_spec p (Fact.out : p.Prime).pos).intermediateField_adjoin_isCyclotomicExtension ℚ
    have instMixedAmbientCycloEll : IsCyclotomicExtension {ell} ℚ Ce :=
      (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos).intermediateField_adjoin_isCyclotomicExtension ℚ
    have h := IntermediateField.isCyclotomicExtension_lcm_sup ℚ A3.Omega p ell Cp Ce
    rw [hcop.lcm_eq_mul] at h
    convert h using 1
  have instMixedAmbientNumberM : NumberField M := IsCyclotomicExtension.numberField {p * ell} ℚ M
  have hpM : A3.primitiveRoot p ∈ M :=
    (show Cp ≤ M from le_sup_left) (IntermediateField.subset_adjoin ℚ _ (by simp))
  have heM : A3.primitiveRoot ell ∈ M :=
    (show Ce ≤ M from le_sup_right) (IntermediateField.subset_adjoin ℚ _ (by simp))
  let b := Nat.chineseRemainder hcop 1 (s : ZMod ell).val
  have hbp : b.val.Coprime p := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.1, ZMod.coprime_mod_iff_coprime]
    exact Nat.coprime_one_left p
  have hbe : b.val.Coprime ell := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.2, ZMod.coprime_mod_iff_coprime]
    exact ZMod.val_coe_unit_coprime s
  let t : (ZMod (p * ell))ˣ := ZMod.unitOfCoprime b.val (hbp.mul_right hbe)
  let sigmaM := (IsCyclotomicExtension.Rat.galEquivZMod (p * ell) M).symm t
  have hsigmaM (x : M) (hx : x ^ (p * ell) = 1) : sigmaM x = x ^ b.val := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (p * ell) M sigmaM hx
    simp only [sigmaM, MulEquiv.apply_symm_apply, t, ZMod.coe_unitOfCoprime,
      ZMod.val_natCast] at h
    exact h.trans (pow_eq_pow_mod b.val hx).symm
  let sigma := sigmaM.liftNormal A3.Omega
  have hlift (x : A3.Omega) (hx : x ∈ M) (hxN : x ^ (p * ell) = 1) :
      sigma x = x ^ b.val := by
    let y : M := ⟨x, hx⟩
    have hy : y ^ (p * ell) = 1 := Subtype.ext hxN
    calc
      sigma x = algebraMap M A3.Omega (sigmaM y) := sigmaM.liftNormal_commutes A3.Omega y
      _ = x ^ b.val := by rw [hsigmaM y hy, map_pow]; rfl
  refine ⟨sigma, ?_, ?_⟩
  · have hpz := (A3.primitiveRoot_spec p (Fact.out : p.Prime).pos).pow_eq_one
    rw [hlift _ hpM (by rw [pow_mul, hpz, one_pow]), pow_eq_pow_mod b.val hpz,
      b.prop.1, ← pow_eq_pow_mod 1 hpz, pow_one]
  · have hez := (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos).pow_eq_one
    rw [hlift _ heM (by rw [mul_comm p ell, pow_mul, hez, one_pow]),
      pow_eq_pow_mod b.val hez, b.prop.2, ← pow_eq_pow_mod (s : ZMod ell).val hez]

private lemma mixed_primitive (p ell : ℕ) (hp : 0 < p) :
    IsPrimitiveRoot (mixedPRoot p ell) p := by
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
  exact A3.primitiveRoot_spec p hp

private lemma mixed_root_ne_inv
    (p ell : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    mixedPRoot p ell ≠ (mixedPRoot p ell)⁻¹ := by
  intro h
  have hp := (Fact.out : p.Prime)
  have hr := mixed_primitive p ell hp.pos
  have hpow : mixedPRoot p ell ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [h]
    exact inv_mul_cancel₀ (hr.ne_zero hp.ne_zero)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) (hr.dvd_of_pow_eq_one 2 hpow)
  exact hp2 (Nat.le_antisymm hle hp.two_le)

private lemma exists_mixed_reversing
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell) :
    ∃ tau : mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell,
      tau (mixedPRoot p ell) = (mixedPRoot p ell)⁻¹ := by
  have hp := (Fact.out : p.Prime)
  have instMixedReverseNeP : NeZero p := ⟨hp.ne_zero⟩
  have instMixedReverseCyclo : IsCyclotomicExtension {p} (A3.Bsub p ell) (mixedExtension p ell) :=
    mixedExtension_isCyclotomic p ell hp.pos
  have instMixedReverseGalois : IsGalois (A3.Bsub p ell) (mixedExtension p ell) :=
    IsCyclotomicExtension.isGalois {p} (A3.Bsub p ell) (mixedExtension p ell)
  obtain ⟨sigma, hsige, hsigp⟩ := mixed_ambient_action ell p hpe.symm (-1)
  have hval : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
    simp only [Units.val_neg, Units.val_one, ZMod.val_neg_of_ne_zero, ZMod.val_one]
  have hpinv : sigma (A3.primitiveRoot p) = (A3.primitiveRoot p)⁻¹ := by
    rw [hsigp, hval]
    have hr := A3.primitiveRoot_spec p hp.pos
    calc
      A3.primitiveRoot p ^ (p - 1) =
          A3.primitiveRoot p ^ (p - 1) *
            (A3.primitiveRoot p * (A3.primitiveRoot p)⁻¹) := by
        rw [mul_inv_cancel₀ (hr.ne_zero hp.ne_zero), mul_one]
      _ = (A3.primitiveRoot p)⁻¹ := by
        rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.one_le, hr.pow_eq_one, one_mul]
  have hfixF (x : A3.F p) : sigma (x : A3.Omega) = (x : A3.Omega) := by
    have heq : sigma.toAlgHom.comp (A3.Fsub p).val = (A3.Fsub p).val := by
      apply IntermediateField.adjoin_algHom_ext
      intro y hy
      obtain rfl : y = A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹ := by simpa using hy
      change sigma (A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹) =
        A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹
      rw [map_add, map_inv₀, hpinv, inv_inv, add_comm]
    exact DFunLike.congr_fun heq x
  let sigmaF : A3.Omega ≃ₐ[A3.F p] A3.Omega :=
    AlgEquiv.ofRingEquiv (f := sigma.toRingEquiv) hfixF
  have hfixB (x : A3.Bsub p ell) : sigma (x : A3.Omega) = (x : A3.Omega) := by
    have heq : sigmaF.toAlgHom.comp (A3.Bsub p ell).val = (A3.Bsub p ell).val := by
      apply IntermediateField.adjoin_algHom_ext
      intro y hy
      obtain rfl : y = A3.primitiveRoot ell := by simpa using hy
      exact hsige
    exact DFunLike.congr_fun heq x
  let sigmaB : A3.Omega ≃ₐ[A3.Bsub p ell] A3.Omega :=
    AlgEquiv.ofRingEquiv (f := sigma.toRingEquiv) hfixB
  let tau := sigmaB.restrictNormal (mixedExtension p ell)
  refine ⟨tau, ?_⟩
  apply Subtype.ext
  have h := sigmaB.restrictNormal_commutes (mixedExtension p ell) (mixedPRoot p ell)
  change ((tau (mixedPRoot p ell) : mixedExtension p ell) : A3.Omega) =
    sigma (A3.primitiveRoot p) at h
  exact h.trans hpinv


lemma mixedExtension_finrank
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    Module.finrank (A3.Bsub p ell) (mixedExtension p ell) = 2 := by
  have hp := (Fact.out : p.Prime)
  let t : A3.Bsub p ell := algebraMap (A3.F p) (A3.Bsub p ell)
    ⟨A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let P : Polynomial (A3.Bsub p ell) := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1
  have hP2 : P.coeff 2 = 1 := by norm_num [P, Polynomial.coeff_one]
  have hPne : P ≠ 0 := by intro h; rw [h, Polynomial.coeff_zero] at hP2; exact zero_ne_one hP2
  have hPdeg : P.natDegree ≤ 2 := by dsimp [P]; compute_degree
  have hPzero : Polynomial.aeval (A3.primitiveRoot p) P = 0 := by
    have hz0 : A3.primitiveRoot p ≠ 0 := (A3.primitiveRoot_spec p hp.pos).ne_zero hp.ne_zero
    simp only [P, map_add, map_sub, map_pow, map_mul, map_one, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change A3.primitiveRoot p ^ 2 -
      (A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹) * A3.primitiveRoot p + 1 = 0
    field_simp
    ring
  have hzint : IsIntegral (A3.Bsub p ell) (A3.primitiveRoot p) :=
    ((A3.primitiveRoot_spec p hp.pos).isIntegral hp.pos).tower_top
  have hle : Module.finrank (A3.Bsub p ell) (mixedExtension p ell) ≤ 2 := by
    rw [mixedExtension, IntermediateField.adjoin.finrank hzint]
    exact (Polynomial.natDegree_le_of_dvd
      (minpoly.dvd (A3.Bsub p ell) (A3.primitiveRoot p) hPzero) hPne).trans hPdeg
  have hne : Module.finrank (A3.Bsub p ell) (mixedExtension p ell) ≠ 1 := by
    intro h1
    change Module.finrank (A3.Bsub p ell)
      (IntermediateField.adjoin (A3.Bsub p ell) {A3.primitiveRoot p}) = 1 at h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1)
    have hroot : algebraMap (A3.Bsub p ell) (mixedExtension p ell) y = mixedPRoot p ell :=
      Subtype.ext hy
    obtain ⟨tau, htau⟩ := exists_mixed_reversing p ell hpe
    have hfixed : tau (mixedPRoot p ell) = mixedPRoot p ell := by
      rw [← hroot, tau.commutes]
    exact mixed_root_ne_inv p ell hp2 (hfixed.symm.trans htau)
  have hpos := (Module.finrank_pos : 0 < Module.finrank (A3.Bsub p ell) (mixedExtension p ell))
  omega

lemma exists_mixed_involution
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    ∃ tau : mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell,
      tau (mixedPRoot p ell) = (mixedPRoot p ell)⁻¹ ∧
      (∀ x : mixedExtension p ell, tau (tau x) = x) ∧
      ∀ x : mixedExtension p ell, tau x = x ↔
        ∃ y : A3.Bsub p ell, algebraMap (A3.Bsub p ell) (mixedExtension p ell) y = x := by
  have hp := (Fact.out : p.Prime)
  have instMixedInvolutionCyclo : IsCyclotomicExtension {p} (A3.Bsub p ell) (mixedExtension p ell) :=
    mixedExtension_isCyclotomic p ell hp.pos
  have instMixedInvolutionGalois : IsGalois (A3.Bsub p ell) (mixedExtension p ell) :=
    IsCyclotomicExtension.isGalois {p} (A3.Bsub p ell) (mixedExtension p ell)
  obtain ⟨tau, htau⟩ := exists_mixed_reversing p ell hpe
  have htau_ne : tau ≠ 1 := by
    intro h
    apply mixed_root_ne_inv p ell hp2
    simpa only [h, AlgEquiv.one_apply] using htau
  have hcard : Nat.card (mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, mixedExtension_finrank p ell hp2 hpe]
  obtain ⟨rho, hrho, huniq⟩ := (Nat.card_eq_two_iff' (1 :
    mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell)).mp hcard
  have hcases (f : mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell) :
      f = 1 ∨ f = tau := by
    by_cases hf : f = 1
    · exact Or.inl hf
    · exact Or.inr ((huniq f hf).trans (huniq tau htau_ne).symm)
  have htau_sq : tau * tau = 1 := by
    have hinv : tau⁻¹ = tau := ((hcases tau⁻¹).resolve_left (inv_ne_one.mpr htau_ne))
    nth_rw 1 [← hinv]
    exact inv_mul_cancel tau
  refine ⟨tau, htau, ?_, ?_⟩
  · intro x
    exact congrArg (fun f : mixedExtension p ell ≃ₐ[A3.Bsub p ell] mixedExtension p ell => f x) htau_sq
  · intro x
    constructor
    · intro hx
      apply (IsGalois.mem_range_algebraMap_iff_fixed (F := A3.Bsub p ell) x).mpr
      intro f
      rcases hcases f with rfl | rfl
      · rfl
      · exact hx
    · rintro ⟨y, rfl⟩
      exact tau.commutes y

end Catalan.Thaine
