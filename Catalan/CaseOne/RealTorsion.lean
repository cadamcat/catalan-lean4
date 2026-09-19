import Catalan.CaseOne.TorsionReduction

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitQuotient
variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

lemma real_units_pow_injective (q : ℕ) (hq : Odd q) :
    Function.Injective (fun u : (𝓞 K)ˣ => u ^ q) := by
  intro a b hab
  let w0 : InfinitePlace K := NumberField.Units.dirichletUnitTheorem.w₀
  let φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal
    (NumberField.IsTotallyReal.isReal w0)
  have hab' : (φ ((a : 𝓞 K) : K)) ^ q = (φ ((b : 𝓞 K) : K)) ^ q := by
    have h := congrArg (fun u : (𝓞 K)ˣ => φ ((u : 𝓞 K) : K)) hab
    change φ (((a : 𝓞 K) ^ q : 𝓞 K) : K) =
      φ (((b : 𝓞 K) ^ q : 𝓞 K) : K) at h
    simpa only [map_pow] using h
  have huv : φ ((a : 𝓞 K) : K) = φ ((b : 𝓞 K) : K) := hq.pow_injective hab'
  have huv' : ((a : 𝓞 K) : K) = ((b : 𝓞 K) : K) := φ.injective huv
  apply Units.ext
  exact NumberField.RingOfIntegers.coe_injective huv'

lemma real_torsion_le_qPowers (q : ℕ) (hq : Odd q) :
    NumberField.Units.torsion K ≤ qPowers (𝓞 K)ˣ q := by
  intro u hu
  have hinj : Function.Injective (fun a : NumberField.Units.torsion K => a ^ q) := by
    intro a b hab
    apply Subtype.ext
    exact real_units_pow_injective K q hq (congrArg Subtype.val hab)
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
  exact ⟨(v : (𝓞 K)ˣ), congrArg Subtype.val hv⟩

end Catalan.UnitQuotient
