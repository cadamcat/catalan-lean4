module

public import Catalan.Density.Definitions
public import Mathlib

/-!
# `Catalan.Thaine.PrimeNormProduct`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators Pointwise
noncomputable section
namespace Catalan.Thaine

private lemma prod_smul_eq_orbit_pow
    (G X M : Type*) [Group G] [Fintype G] [MulAction G X] [CommMonoid M]
    (x : X) (f : X → M) :
    (∏ g : G, f (g • x)) =
      ∏ᶠ y : MulAction.orbit G x, f y.val ^ Nat.card (MulAction.stabilizer G x) := by
  classical
  let instWeightedOrbitFintype : Fintype (MulAction.orbit G x) :=
    (Finite.finite_mulAction_orbit (M := G) x).fintype
  let o : G → MulAction.orbit G x := fun g => ⟨g • x, MulAction.mem_orbit _ _⟩
  have hcard (y : MulAction.orbit G x) :
      Fintype.card {g : G // o g = y} = Nat.card (MulAction.stabilizer G x) := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
    let e : {h : G // o h = y} ≃ MulAction.stabilizer G x :=
      { toFun := fun h => ⟨g⁻¹ * h.val, by
          apply MulAction.mem_stabilizer_iff.mpr
          have hh := congrArg Subtype.val h.property
          change h.val • x = y.val at hh
          rw [mul_smul, hh, ← hg, inv_smul_smul]⟩
        invFun := fun h => ⟨g * h.val, by
          apply Subtype.ext
          change (g * h.val) • x = y.val
          rw [mul_smul, MulAction.mem_stabilizer_iff.mp h.property, hg]⟩
        left_inv := by intro h; apply Subtype.ext; simp
        right_inv := by intro h; apply Subtype.ext; simp }
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  rw [finprod_eq_prod_of_fintype]
  calc
    (∏ g : G, f (g • x)) =
        ∏ y : MulAction.orbit G x, ∏ _h : {g : G // o g = y}, f y.val :=
      (Fintype.prod_fiberwise' o (fun y => f y.val)).symm
    _ = ∏ y : MulAction.orbit G x, f y.val ^ Nat.card (MulAction.stabilizer G x) := by
      apply Finset.prod_congr rfl
      intro y hy
      rw [Finset.prod_const, Finset.card_univ, hcard y]

lemma galois_prime_norm_product
    (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (∏ᶠ g : F ≃ₐ[ℚ] F, Ideal.map (A3.integralAut g).toRingHom v.asIdeal) =
      Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.relNorm ℤ v.asIdeal) := by
  classical
  let G := F ≃ₐ[ℚ] F
  let instPrimeNormGalFintype : Fintype G := Fintype.ofFinite _
  let r : Ideal ℤ := v.asIdeal.under ℤ
  have instPrimeNormBaseMax : r.IsMaximal := inferInstance
  have instPrimeNormOver : v.asIdeal.LiesOver r := inferInstance
  have hrne : r ≠ ⊥ := Ideal.under_ne_bot ℤ v.ne_bot
  let instPrimeNormBaseQuotFinite : Finite (ℤ ⧸ r) :=
    Ring.HasFiniteQuotients.finiteQuotient hrne
  let instPrimeNormFiberFintype : Fintype (r.primesOver (𝓞 F)) :=
    (Algebra.QuasiFinite.finite_primesOver r).fintype
  have horbit : MulAction.orbit G v.asIdeal = r.primesOver (𝓞 F) :=
    Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 F) G r v.asIdeal
  have hstab : Nat.card (MulAction.stabilizer G v.asIdeal) =
      v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ := by
    rw [Ideal.card_stabilizer_eq (G := G) r v.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx r v.asIdeal G,
      Ideal.inertiaDegIn_eq_inertiaDeg r v.asIdeal G]
  have he (Q : r.primesOver (𝓞 F)) : Q.1.ramificationIdx ℤ = v.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup r Q.1 v.asIdeal G
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) r =
      ∏ Q : r.primesOver (𝓞 F), Q.1 ^ Q.1.ramificationIdx ℤ := by
    exact (Ideal.map_algebraMap_eq_finsetProd_pow hrne).trans
      (Finset.prod_set_coe (f := fun Q : Ideal (𝓞 F) => Q ^ Q.ramificationIdx ℤ)
        (r.primesOver (𝓞 F))).symm
  have hnorm : Ideal.relNorm ℤ v.asIdeal = r ^ v.asIdeal.inertiaDeg ℤ :=
    Ideal.relNorm_eq_pow_of_isMaximal v.asIdeal r
  have hsmul (g : G) : Ideal.map (A3.integralAut g).toRingHom v.asIdeal = g • v.asIdeal := by
    rw [Ideal.pointwise_smul_def]
    rfl
  calc
    (∏ᶠ g : F ≃ₐ[ℚ] F, Ideal.map (A3.integralAut g).toRingHom v.asIdeal) =
        ∏ g : G, g • v.asIdeal := by
      rw [finprod_eq_prod_of_fintype]
      exact Finset.prod_congr rfl (fun g hg => hsmul g)
    _ = ∏ᶠ Q : MulAction.orbit G v.asIdeal,
        Q.1 ^ Nat.card (MulAction.stabilizer G v.asIdeal) :=
      prod_smul_eq_orbit_pow G (Ideal (𝓞 F)) (Ideal (𝓞 F)) v.asIdeal id
    _ = ∏ᶠ Q : r.primesOver (𝓞 F),
        Q.1 ^ (v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ) := by rw [horbit, hstab]
    _ = (∏ Q : r.primesOver (𝓞 F), Q.1 ^ Q.1.ramificationIdx ℤ) ^
        v.asIdeal.inertiaDeg ℤ := by
      rw [finprod_eq_prod_of_fintype, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro Q hQ
      rw [he Q, pow_mul]
    _ = (Ideal.map (algebraMap ℤ (𝓞 F)) r) ^ v.asIdeal.inertiaDeg ℤ := by rw [hmap]
    _ = Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.relNorm ℤ v.asIdeal) := by rw [hnorm, Ideal.map_pow]

end Catalan.Thaine
