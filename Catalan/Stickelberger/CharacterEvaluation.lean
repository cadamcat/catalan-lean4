module

public import Catalan.Stickelberger.CharacterDefs
public import Catalan.Stickelberger.CharacterRecovery

/-!
# `Catalan.Stickelberger.CharacterEvaluation`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.MinusIndependence
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma characterOnG_sigma_inv (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    characterOnG p K χ ((σ p K a)⁻¹) = χ (a : ZMod p) := by
  let pNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  change χ ((((IsCyclotomicExtension.Rat.galEquivZMod p K)
    ((σ p K a)⁻¹))⁻¹ : (ZMod p)ˣ) : ZMod p) = χ (a : ZMod p)
  rw [map_inv]
  simp only [σ, MulEquiv.apply_symm_apply, inv_inv]

lemma characterEval_coeff (χ : DirichletCharacter ℂ p) (T : ComplexRing p K) :
    characterEval p K χ T =
      ∑ a : (ZMod p)ˣ, T.coeff ((σ p K a)⁻¹) * χ (a : ZMod p) := by
  classical
  let galFintype : Fintype (G p K) := Fintype.ofFinite _
  have hbij : Function.Bijective (fun a : (ZMod p)ˣ => (σ p K a)⁻¹) :=
    (Equiv.inv (G p K)).bijective.comp (σ_bijective p K)
  calc
    characterEval p K χ T = ∑ g : G p K, T.coeff g * characterOnG p K χ g := by
      rw [characterEval, MonoidAlgebra.lift_apply']
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      rfl
    _ = ∑ a : (ZMod p)ˣ, T.coeff ((σ p K a)⁻¹) * characterOnG p K χ ((σ p K a)⁻¹) :=
      (hbij.sum_comp _).symm
    _ = _ := by simp only [characterOnG_sigma_inv]

lemma characterEval_PTheta (χ : DirichletCharacter ℂ p) :
    characterEval p K χ (complexPTheta p K) =
      ∑ a : ZMod p, (a.val : ℂ) * χ a := by
  classical
  simp only [characterEval_coeff, complexPTheta, coeffCast_coeff, pθ_coeff, Int.cast_natCast]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : ZMod p)]
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  exact Fintype.sum_equiv (unitsEquivNeZero : (ZMod p)ˣ ≃ {a : ZMod p // a ≠ 0})
    _ _ (fun _ => rfl)

lemma characterEval_minus (χ : DirichletCharacter ℂ p) :
    characterEval p K χ (complexMinus p K) = 1 - χ (-1) := by
  let pNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hi : (σ p K (-1 : (ZMod p)ˣ))⁻¹ = ι p K := by
    change ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm (-1))⁻¹ =
      (IsCyclotomicExtension.Rat.galEquivZMod p K).symm (-1)
    rw [← map_inv]
    simp
  have hv : characterOnG p K χ (ι p K) = χ (-1) := by
    rw [← hi]
    exact characterOnG_sigma_inv p K χ (-1)
  rw [complexMinus, map_sub, coeffCast_single, coeffCast_single, map_sub]
  simp only [Int.cast_one, characterEval, MonoidAlgebra.lift_single, one_smul, map_one, hv]

lemma characterEval_joint_injective :
    Function.Injective (fun T : ComplexRing p K => fun χ : DirichletCharacter ℂ p =>
      characterEval p K χ T) := by
  intro T U h
  have hc : (fun a : (ZMod p)ˣ => T.coeff ((σ p K a)⁻¹)) =
      (fun a : (ZMod p)ˣ => U.coeff ((σ p K a)⁻¹)) := by
    apply unit_character_transform_injective p
    funext χ
    dsimp only
    rw [← characterEval_coeff, ← characterEval_coeff]
    exact congrFun h χ
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  obtain ⟨a, ha⟩ := (σ_bijective p K).surjective g⁻¹
  have hg : g = (σ p K a)⁻¹ := by rw [ha]; simp
  rw [hg]
  exact congrFun hc a

lemma complexPTheta_mul_eq_zero (T : ComplexRing p K) (hT : T ∈ minusRange p K)
    (hzero : complexPTheta p K * T = 0) : T = 0 := by
  apply characterEval_joint_injective p K
  funext χ
  dsimp only
  rw [map_zero]
  rcases χ.even_or_odd with hEven | hOdd
  · obtain ⟨A, hA⟩ := hT
    change A * complexMinus p K = T at hA
    rw [← hA, map_mul, characterEval_minus, (show χ (-1) = 1 from hEven), sub_self, mul_zero]
  · have hχ : χ ≠ 1 := by
      intro hc
      have ho : χ (-1) = -1 := hOdd
      have hone : χ (-1) = 1 := by
        rw [hc]
        exact MulChar.one_apply (isUnit_one.neg)
      rw [hone] at ho
      norm_num at ho
    have hP : characterEval p K χ (complexPTheta p K) ≠ 0 := by
      rw [characterEval_PTheta]
      exact odd_character_weighted_sum_ne_zero p χ hχ hOdd
    have hm := congrArg (characterEval p K χ) hzero
    simp only [map_mul, map_zero] at hm
    exact (mul_eq_zero.mp hm).resolve_left hP

end Catalan.MinusIndependence
