import Catalan.Density.NormalM
import Catalan.Density.FiniteM
import Catalan.Density.FStructure

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma isGalois_Msub_rat (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    IsGalois ℚ (Msub p q) := by
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  have instAlgClosureOmega : IsAlgClosure ℚ Omega := ⟨inferInstance, inferInstance⟩
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  have instFiniteM : FiniteDimensional (F p) (Msub p q) := finiteDimensional_Msub p q hq
  have instFiniteRatM : FiniteDimensional ℚ (Msub p q) :=
    FiniteDimensional.trans ℚ (F p) (Msub p q)
  have instNeZeroQ : NeZero q := ⟨hq.ne'⟩
  let A : IntermediateField ℚ Omega := (Msub p q).restrictScalars ℚ
  let S : Set Omega := {primitiveRoot q} ∪ unitRadicals p q
  have hA : A = Fsub p ⊔ IntermediateField.adjoin ℚ S := by
    dsimp only [A, Msub, Bsub, S]
    rw [← IntermediateField.adjoin_union]
    exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ (Fsub p) _
  have hFA : Fsub p ≤ A := by rw [hA]; exact le_sup_left
  have hgen (z : Omega) (hz : z ∈ S) : z ∈ A := by
    rw [hA]
    exact (show IntermediateField.adjoin ℚ S ≤ Fsub p ⊔ IntermediateField.adjoin ℚ S
      from le_sup_right) (IntermediateField.subset_adjoin ℚ S hz)
  have hzeta : primitiveRoot q ∈ A := hgen _ (Or.inl rfl)
  have instNormalRatM : Normal ℚ (Msub p q) := by
    change Normal ℚ A
    apply IntermediateField.normal_iff_forall_map_le'.mpr
    intro σ
    have hFmap : (Fsub p).map σ.toAlgHom ≤ Fsub p :=
      (IntermediateField.normal_iff_forall_map_le').mp
        (inferInstance : Normal ℚ (Fsub p)) σ
    have hSmap : σ '' S ⊆ A := by
      rintro _ ⟨r, hr, rfl⟩
      rcases hr with hr | hr
      · obtain rfl := Set.mem_singleton_iff.mp hr
        have hpow : σ (primitiveRoot q) ^ q = 1 := by
          rw [← map_pow, (primitiveRoot_spec q hq).pow_eq_one, map_one]
        obtain ⟨i, _, hi⟩ := (primitiveRoot_spec q hq).eq_pow_of_pow_eq_one hpow
        rw [← hi]
        exact pow_mem hzeta i
      · obtain ⟨u, hu⟩ := hr
        let τ : F p ≃ₐ[ℚ] F p := σ.restrictNormal (F p)
        let u' : (NumberField.RingOfIntegers (F p))ˣ :=
          Units.mapEquiv (NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv) u
        apply hgen
        right
        refine ⟨u', ?_⟩
        rw [← map_pow, hu]
        change σ (algebraMap (F p) Omega (((u : NumberField.RingOfIntegers (F p)) : F p))) =
          algebraMap (F p) Omega (τ (((u : NumberField.RingOfIntegers (F p)) : F p)))
        exact (AlgEquiv.restrictNormal_commutes σ (F p) _).symm
    calc
      A.map σ.toAlgHom = (Fsub p).map σ.toAlgHom ⊔ IntermediateField.adjoin ℚ (σ '' S) := by
        rw [hA, IntermediateField.map_sup, IntermediateField.adjoin_map]
        rfl
      _ ≤ A := sup_le (hFmap.trans hFA) (IntermediateField.adjoin_le_iff.mpr hSmap)
  exact isGalois_iff.mpr ⟨inferInstance, instNormalRatM⟩

end Catalan.A3
