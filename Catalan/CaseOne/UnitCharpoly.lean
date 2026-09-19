import Catalan.CaseOne.IntegralRepresentation
import Catalan.CaseOne.LogSpaceEquiv
import Catalan.CaseOne.LatticeCharpoly
import Catalan.CaseOne.PowerModN
import Catalan.CaseOne.ModNAction
import Catalan.CaseOne.Regular

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
open UnitQuotient
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

/-- The actual integral Galois action transported to the Dirichlet unit lattice. -/
def logLatticeAction (τ : G p K) : Units.unitLattice K →ₗ[ℤ] Units.unitLattice K :=
  (Units.logEmbeddingEquiv K).conj (integralUnitRepresentation p K τ)

lemma logLatticeAction_intertwining (τ : G p K) (v : Units.unitLattice K) :
    UnitLog.logRealAction K p τ (v : Units.dirichletUnitTheorem.logSpace K) =
      (logLatticeAction p K τ v : Units.dirichletUnitTheorem.logSpace K) := by
  obtain ⟨z, rfl⟩ := (Units.logEmbeddingEquiv K).surjective v
  obtain ⟨u, rfl⟩ := integralUnitClass_surjective K z
  simp only [logLatticeAction, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, integralUnitRepresentation_apply]
  change UnitLog.logRealAction K p τ (Units.logEmbedding K (Additive.ofMul u)) =
    Units.logEmbedding K (Additive.ofMul (Circular.unitAction p K τ u))
  exact UnitLog.logRealAction_logEmbedding K p τ u

lemma integralUnit_charpoly_real (τ : G p K) :
    (UnitLog.logRealAction K p τ).charpoly =
      (integralUnitRepresentation p K τ).charpoly.map (Int.castRingHom ℝ) := by
  classical
  calc
    (UnitLog.logRealAction K p τ).charpoly =
        (logLatticeAction p K τ).charpoly.map (Int.castRingHom ℝ) :=
      UnitLog.charpoly_eq_map_of_lattice_intertwining (Units.unitLattice K)
        (logLatticeAction p K τ) (UnitLog.logRealAction K p τ)
        (logLatticeAction_intertwining p K τ)
    _ = _ := by rw [logLatticeAction, LinearEquiv.charpoly_conj]

noncomputable instance unitPowerModuleFinite (q : ℕ) :
    Module.Finite (ZMod q) (PowerQuotient (𝓞 K)ˣ q) := by
  let f : Additive (𝓞 K)ˣ →ₗ[ℤ] PowerQuotient (𝓞 K)ˣ q :=
    (QuotientGroup.mk' (qPowers (𝓞 K)ˣ q)).toAdditive.toIntLinearMap
  have hs : Function.Surjective f := by
    intro v
    induction v using QuotientGroup.induction_on with
    | _ u => exact ⟨Additive.ofMul u, rfl⟩
  have hfinite : Module.Finite ℤ (PowerQuotient (𝓞 K)ˣ q) := Module.Finite.of_surjective f hs
  exact Module.Finite.of_restrictScalars_finite ℤ (ZMod q) _

/-- Quotienting units and then reducing the actual torsion-free lattice. -/
def unitReductionMap (q : ℕ) : PowerQuotient (𝓞 K)ˣ q →ₗ[ZMod q] ModN (UnitLattice K) q :=
  (powerQuotientModN ((𝓞 K)ˣ ⧸ Units.torsion K) q).toLinearMap.comp (unitTorsionMap K q)

lemma unitReductionMap_apply (q : ℕ) (u : (𝓞 K)ˣ) :
    unitReductionMap K q (powerClass q u) = ModN.mkQ q (integralUnitClass K u) := by
  change powerQuotientModN ((𝓞 K)ˣ ⧸ Units.torsion K) q
      (powerClass q (QuotientGroup.mk u)) = _
  exact powerQuotientModN_apply _ q _

lemma unitReductionMap_intertwining (q : ℕ) (τ : G p K)
    (v : PowerQuotient (𝓞 K)ˣ q) :
    unitReductionMap K q (unitRepresentation p K q τ v) =
      UnitReduction.modNMap (UnitLattice K) q (integralUnitRepresentation p K τ)
        (unitReductionMap K q v) := by
  induction v using QuotientGroup.induction_on with
  | _ u =>
    change unitReductionMap K q (powerMap q (Circular.unitAction p K τ) (powerClass q u)) =
      UnitReduction.modNMap (UnitLattice K) q (integralUnitRepresentation p K τ)
        (unitReductionMap K q (powerClass q u))
    rw [powerMap_apply, unitReductionMap_apply, unitReductionMap_apply,
      UnitReduction.modNMap_apply, integralUnitRepresentation_apply]

lemma unitReductionMap_bijective_of_torsion_le (q : ℕ)
    (hT : Units.torsion K ≤ qPowers (𝓞 K)ˣ q) :
    Function.Bijective (unitReductionMap K q) :=
  (powerQuotientModN ((𝓞 K)ˣ ⧸ Units.torsion K) q).bijective.comp
    (unitTorsionMap_bijective_of_torsion_le K q hT)

lemma unitRepresentation_charpoly_of_torsion_le (q : ℕ) [Fact q.Prime]
    (hT : Units.torsion K ≤ qPowers (𝓞 K)ˣ q) (τ : G p K) :
    (unitRepresentation p K q τ).charpoly =
      (integralUnitRepresentation p K τ).charpoly.map (Int.castRingHom (ZMod q)) := by
  let e := LinearEquiv.ofBijective (unitReductionMap K q)
    (unitReductionMap_bijective_of_torsion_le K q hT)
  have hconj : e.conj (unitRepresentation p K q τ) =
      UnitReduction.modNMap (UnitLattice K) q (integralUnitRepresentation p K τ) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact unitReductionMap_intertwining p K q τ w
  rw [← LinearEquiv.charpoly_conj e, hconj, UnitReduction.modNMap_charpoly]

/-- Actual logarithmic coordinates indexed by the regular Galois action. -/
def logRegularEquiv [IsTotallyReal K] [IsGalois ℚ K] (w : InfinitePlace K) :
    Units.dirichletUnitTheorem.logSpace K ≃ₗ[ℝ] UnitLog.groupZeroSum K :=
  (UnitLog.logSpaceEquiv K).trans (UnitLog.zeroSumRegularEquiv K w)

lemma logRegularEquiv_intertwining [IsTotallyReal K] [IsGalois ℚ K]
    (w : InfinitePlace K) (τ : G p K) (v : Units.dirichletUnitTheorem.logSpace K) :
    logRegularEquiv K w (UnitLog.logRealAction K p τ v) =
      UnitLog.regularZeroSumAction K τ (logRegularEquiv K w v) := by
  change UnitLog.zeroSumRegularEquiv K w
      (UnitLog.logSpaceEquiv K ((UnitLog.logSpaceEquiv K).symm
        (UnitLog.zeroSumAction K p τ (UnitLog.logSpaceEquiv K v)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact UnitLog.zeroSumRegularEquiv_intertwining K w p τ (UnitLog.logSpaceEquiv K v)

lemma integralUnit_charpoly_regular [IsTotallyReal K] [IsGalois ℚ K]
    (w : InfinitePlace K) (τ : G p K) :
    (UnitLog.regularZeroSumAction K τ).charpoly =
      (integralUnitRepresentation p K τ).charpoly.map (Int.castRingHom ℝ) := by
  classical
  let e := logRegularEquiv K w
  have he : e.conj (UnitLog.logRealAction K p τ) = UnitLog.regularZeroSumAction K τ := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact logRegularEquiv_intertwining p K w τ x
  rw [← he, LinearEquiv.charpoly_conj, integralUnit_charpoly_real]

variable [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

lemma unitReductionMap_bijective (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Bijective (unitReductionMap K q) :=
  unitReductionMap_bijective_of_torsion_le K q (torsion_le_qPowers p K q hpq hq2)

def unitReductionEquiv (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    PowerQuotient (𝓞 K)ˣ q ≃ₗ[ZMod q] ModN (UnitLattice K) q :=
  LinearEquiv.ofBijective (unitReductionMap K q) (unitReductionMap_bijective p K q hpq hq2)

lemma unitRepresentation_charpoly (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2)
    (τ : G p K) :
    (unitRepresentation p K q τ).charpoly =
      (integralUnitRepresentation p K τ).charpoly.map (Int.castRingHom (ZMod q)) := by
  exact unitRepresentation_charpoly_of_torsion_le p K q
    (torsion_le_qPowers p K q hpq hq2) τ

end Catalan.UnitModule
