module

public import Catalan.Density.TRelative

/-!
# `Catalan.Density.GaloisModules`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]

@[instance_reducible]
def TGalCommGroup : CommGroup (T p q ≃ₐ[Bsub p q] T p q) :=
  { (inferInstance : Group (T p q ≃ₐ[Bsub p q] T p q)) with
    mul_comm := T_gal_mul_comm p q }

@[instance_reducible]
def HGalCommGroup : CommGroup (Hsub p q ≃ₐ[F p] Hsub p q) :=
  { (inferInstance : Group (Hsub p q ≃ₐ[F p] Hsub p q)) with
    mul_comm := Hsub_gal_mul_comm p q }

attribute [local instance] TGalCommGroup HGalCommGroup kummerGalCommGroup

@[instance_reducible]
def TGalModule : Module (ZMod q) (Additive (T p q ≃ₐ[Bsub p q] T p q)) :=
  AddCommGroup.zmodModule (fun sigma => by
    change (Additive.toMul sigma) ^ q = 1
    exact T_gal_pow_eq_one p q _)

@[instance_reducible]
def HGalModule : Module (ZMod q) (Additive (Hsub p q ≃ₐ[F p] Hsub p q)) :=
  AddCommGroup.zmodModule (fun sigma => by
    change (Additive.toMul sigma) ^ q = 1
    exact Hsub_gal_pow_eq_one p q _)

attribute [local instance] TGalModule HGalModule kummerGalModule

def restrictTToM : (T p q ≃ₐ[Bsub p q] T p q) →* (Msub p q ≃ₐ[Bsub p q] Msub p q) := by
  have instGaloisM : IsGalois (Bsub p q) (Msub p q) :=
    isGalois_Msub_over_B p q (Fact.out : q.Prime).pos
  exact AlgEquiv.restrictNormalHom (Msub p q)

def restrictTToH : (T p q ≃ₐ[Bsub p q] T p q) →* (Hsub p q ≃ₐ[F p] Hsub p q) := by
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  exact (AlgEquiv.restrictNormalHom (Hsub p q)).comp (AlgEquiv.restrictScalarsHom (F p))

lemma restrictTToM_commutes (sigma : T p q ≃ₐ[Bsub p q] T p q) (x : Msub p q) :
    algebraMap (Msub p q) (T p q) (restrictTToM p q sigma x) =
      sigma (algebraMap (Msub p q) (T p q) x) := by
  have instGaloisM : IsGalois (Bsub p q) (Msub p q) :=
    isGalois_Msub_over_B p q (Fact.out : q.Prime).pos
  exact sigma.restrictNormal_commutes (Msub p q) x

omit [Fact q.Prime] in
lemma restrictTToH_commutes (sigma : T p q ≃ₐ[Bsub p q] T p q) (x : Hsub p q) :
    algebraMap (Hsub p q) (T p q) (restrictTToH p q sigma x) =
      sigma (algebraMap (Hsub p q) (T p q) x) := by
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  exact (sigma.restrictScalars (F p)).restrictNormal_commutes (Hsub p q) x

def TToMLinear : Additive (T p q ≃ₐ[Bsub p q] T p q) →ₗ[ZMod q]
    Additive (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
  (restrictTToM p q).toAdditive.toZModLinearMap q

def TToHLinear : Additive (T p q ≃ₐ[Bsub p q] T p q) →ₗ[ZMod q]
    Additive (Hsub p q ≃ₐ[F p] Hsub p q) :=
  (restrictTToH p q).toAdditive.toZModLinearMap q

lemma TToMLinear_surjective : Function.Surjective (TToMLinear p q) := by
  intro tau
  obtain ⟨sigma, hsigma⟩ := exists_T_lift p q (Fact.out : q.Prime).pos (Additive.toMul tau)
  refine ⟨Additive.ofMul sigma, ?_⟩
  apply Additive.toMul.injective
  change restrictTToM p q sigma = Additive.toMul tau
  apply AlgEquiv.ext
  intro x
  apply (algebraMap (Msub p q) (T p q)).injective
  rw [restrictTToM_commutes, hsigma]

end Catalan.A3
