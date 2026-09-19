import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction
variable (M : Type*) [AddCommGroup M] (q : ℕ)

noncomputable def modNMap (f : M →ₗ[ℤ] M) : ModN M q →ₗ[ZMod q] ModN M q :=
  ModN.liftEquiv'.symm ⟨(ModN.mkQ q).comp f.toAddMonoidHom, fun x => by
    change q • ModN.mkQ q (f x) = 0
    rw [← map_nsmul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨f x, by simp⟩⟩

lemma modNMap_apply (f : M →ₗ[ℤ] M) (x : M) :
    modNMap M q f (ModN.mkQ q x) = ModN.mkQ q (f x) := rfl

open scoped BigOperators in
private lemma modN_basis_repr_mkQ [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) (x : M) (i : ι) :
    (ModN.basis (n := q) b).repr (ModN.mkQ q x) i = (b.repr x i : ZMod q) := by
  have hx : ModN.mkQ q x =
      ∑ j, (b.repr x j : ZMod q) • (ModN.basis (n := q) b) j := by
    calc
      ModN.mkQ q x = ModN.mkQ q (∑ j, b.repr x j • b j) :=
        congrArg (ModN.mkQ q) (b.sum_repr x).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_zsmul, ModN.basis_apply_eq_mkQ, Int.cast_smul_eq_zsmul]
  rw [hx]
  exact congrFun ((ModN.basis (n := q) b).repr_sum_self (fun j => (b.repr x j : ZMod q))) i

lemma modNMap_toMatrix [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) (f : M →ₗ[ℤ] M) :
    LinearMap.toMatrix (ModN.basis (n := q) b) (ModN.basis (n := q) b) (modNMap M q f) =
      (LinearMap.toMatrix b b f).map (Int.castRingHom (ZMod q)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, ModN.basis_apply_eq_mkQ, modNMap_apply,
    modN_basis_repr_mkQ]
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]
  rfl

noncomputable instance modNModuleFree [NeZero q] [Module.Free ℤ M] :
    Module.Free (ZMod q) (ModN M q) :=
  Module.Free.of_basis (ModN.basis (n := q) (Module.Free.chooseBasis ℤ M))

lemma modNMap_charpoly [NeZero q] [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : M →ₗ[ℤ] M) :
    (modNMap M q f).charpoly = f.charpoly.map (Int.castRingHom (ZMod q)) := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  rw [← LinearMap.charpoly_toMatrix (modNMap M q f) (ModN.basis (n := q) b),
    modNMap_toMatrix, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

end Catalan.UnitReduction
