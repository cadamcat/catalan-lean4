module

public import Catalan.Density.RealF

/-!
# `Catalan.Density.FStructure`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

private def fullField (p : ℕ) : IntermediateField ℚ Omega :=
  IntermediateField.adjoin ℚ {primitiveRoot p}

private lemma real_le_full (p : ℕ) : Fsub p ≤ fullField p := by
  rw [Fsub, IntermediateField.adjoin_le_iff]
  rintro x (rfl : x = _)
  have hz : primitiveRoot p ∈ fullField p := IntermediateField.subset_adjoin ℚ _ (by simp)
  exact (fullField p).add_mem hz ((fullField p).inv_mem hz)

private lemma cyclotomic_full (p : ℕ) (hp : 0 < p) :
    IsCyclotomicExtension {p} ℚ (fullField p) := by
  have instNonzeroP : NeZero p := ⟨hp.ne'⟩
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  exact (primitiveRoot_spec p hp).intermediateField_adjoin_isCyclotomicExtension ℚ

private instance finite_full (p : ℕ) : FiniteDimensional ℚ (fullField p) := by
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  apply IntermediateField.finiteDimensional_adjoin
  intro z _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).isIntegral

private instance numberField_full (p : ℕ) : NumberField (fullField p) := {}

lemma isAbelianGalois_F (p : ℕ) (hp : 0 < p) : IsAbelianGalois ℚ (F p) := by
  have instCyclotomicFull : IsCyclotomicExtension {p} ℚ (fullField p) := cyclotomic_full p hp
  have instAbelianFull : IsAbelianGalois ℚ (fullField p) :=
    IsCyclotomicExtension.isAbelianGalois {p} ℚ (fullField p)
  let f : F p →ₐ[ℚ] fullField p := IntermediateField.inclusion (real_le_full p)
  exact IsAbelianGalois.of_algHom f

private lemma primitiveRoot_not_mem_real (p : ℕ) (hp : 2 < p) :
    primitiveRoot p ∉ Fsub p := by
  intro hz
  have instTotallyRealF : NumberField.IsTotallyReal (F p) := isTotallyReal_F p (by omega)
  let z : F p := ⟨primitiveRoot p, hz⟩
  have hzprim : IsPrimitiveRoot z p := by
    apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
    exact primitiveRoot_spec p (by omega)
  have hzero := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hp hzprim
  have hpos := (Module.finrank_pos : 0 < Module.finrank ℚ (F p))
  rw [NumberField.IsTotallyReal.finrank, hzero] at hpos
  omega

lemma finrank_F (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Module.finrank ℚ (F p) = (p - 1) / 2 := by
  have instNonzeroP : NeZero p := ⟨hp.ne_zero⟩
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  let E : IntermediateField (F p) Omega := IntermediateField.adjoin (F p) {primitiveRoot p}
  have hzint : IsIntegral (F p) (primitiveRoot p) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (primitiveRoot p)).isIntegral.tower_top
  have instFiniteE : FiniteDimensional (F p) E := IntermediateField.adjoin.finiteDimensional hzint
  let t : F p := ⟨primitiveRoot p + (primitiveRoot p)⁻¹,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let P : Polynomial (F p) := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1
  have hP2 : P.coeff 2 = 1 := by norm_num [P, Polynomial.coeff_one]
  have hPne : P ≠ 0 := by intro h; rw [h, Polynomial.coeff_zero] at hP2; exact zero_ne_one hP2
  have hPdeg : P.natDegree ≤ 2 := by
    dsimp [P]
    compute_degree
  have hPzero : Polynomial.aeval (primitiveRoot p) P = 0 := by
    have hz0 : primitiveRoot p ≠ 0 := (primitiveRoot_spec p hp.pos).ne_zero hp.ne_zero
    simp only [P, map_add, map_sub, map_pow, map_mul, map_one, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change primitiveRoot p ^ 2 - (primitiveRoot p + (primitiveRoot p)⁻¹) * primitiveRoot p + 1 = 0
    field_simp
    ring
  have hle : Module.finrank (F p) E ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hzint]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd (F p) (primitiveRoot p) hPzero) hPne).trans hPdeg
  have hne : Module.finrank (F p) E ≠ 1 := by
    intro h1
    have hzbot := IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hzbot
    apply primitiveRoot_not_mem_real p (by have := hp.two_le; omega)
    rw [← hz]
    exact z.property
  have htwo : Module.finrank (F p) E = 2 := by
    have hpos := (Module.finrank_pos : 0 < Module.finrank (F p) E)
    omega
  have hE : E.restrictScalars ℚ = fullField p := by
    calc
      E.restrictScalars ℚ = Fsub p ⊔ fullField p :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ (Fsub p) {primitiveRoot p}
      _ = fullField p := sup_eq_right.mpr (real_le_full p)
  have hdegree : Module.finrank ℚ E = p - 1 := by
    change Module.finrank ℚ (E.restrictScalars ℚ) = p - 1
    rw [hE]
    have instCyclotomicFull : IsCyclotomicExtension {p} ℚ (fullField p) := cyclotomic_full p hp.pos
    rw [IsCyclotomicExtension.Rat.finrank p, Nat.totient_prime hp]
  have hmul := Module.finrank_mul_finrank ℚ (F p) E
  rw [htwo, hdegree] at hmul
  omega

lemma gal_F_cyclic (p : ℕ) (hp : p.Prime) : IsCyclic (F p ≃ₐ[ℚ] F p) := by
  have instPrimeP : Fact p.Prime := ⟨hp⟩
  have instNonzeroP : NeZero p := ⟨hp.ne_zero⟩
  have instCyclotomicFull : IsCyclotomicExtension {p} ℚ (fullField p) := cyclotomic_full p hp.pos
  have instAbelianFull : IsAbelianGalois ℚ (fullField p) :=
    IsCyclotomicExtension.isAbelianGalois {p} ℚ (fullField p)
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp.pos
  let f : F p →ₐ[ℚ] fullField p := IntermediateField.inclusion (real_le_full p)
  let instAlgebraFfull : Algebra (F p) (fullField p) := f.toRingHom.toAlgebra
  have instTowerFfull : IsScalarTower ℚ (F p) (fullField p) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have instCyclicFull : IsCyclic (fullField p ≃ₐ[ℚ] fullField p) :=
    (IsCyclotomicExtension.Rat.galEquivZMod p (fullField p)).isCyclic.mpr inferInstance
  exact isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F p) :
    (fullField p ≃ₐ[ℚ] fullField p) →* (F p ≃ₐ[ℚ] F p))
    (AlgEquiv.restrictNormalHom_surjective (fullField p))

lemma card_gal_F (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (F p ≃ₐ[ℚ] F p) = (p - 1) / 2 := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp.pos
  rw [IsGalois.card_aut_eq_finrank, finrank_F p hp hp2]

end Catalan.A3
