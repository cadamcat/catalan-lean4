import Catalan.Stickelberger.MinusSpan
import Catalan.Stickelberger.CharacterSpecialValue

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.MinusIndependence

abbrev ComplexRing (p : ℕ) (K : Type*) [Field K] [NumberField K] :=
  MonoidAlgebra ℂ (G p K)

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

def coeffCast : R p K →+* ComplexRing p K :=
  MonoidAlgebra.mapRingHom (G p K) (Int.castRingHom ℂ)

def characterOnG (χ : DirichletCharacter ℂ p) : G p K →* ℂ := by
  have instCharacterNeZero : NeZero p := ⟨hp.out.ne_zero⟩
  exact (Units.coeHom ℂ).comp (χ.toUnitHom.comp
    ((invMonoidHom : (ZMod p)ˣ →* (ZMod p)ˣ).comp
      (IsCyclotomicExtension.Rat.galEquivZMod p K).toMonoidHom))

def characterEval (χ : DirichletCharacter ℂ p) : ComplexRing p K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ (G p K) (characterOnG p K χ)

def complexPTheta : ComplexRing p K := coeffCast p K (pθ p K)

def complexMinus : ComplexRing p K :=
  coeffCast p K (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1)

def minusRange : Submodule ℂ (ComplexRing p K) :=
  LinearMap.range (LinearMap.mulRight ℂ (complexMinus p K))

def halfUnit (i : Fin ((p - 1) / 2)) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (i.val + 1) ((hp.out.coprime_iff_not_dvd.mpr (by
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by have := i.isLt; omega))).symm)

def halfVector (i : Fin ((p - 1) / 2)) : ComplexRing p K :=
  MonoidAlgebra.single (σ p K (halfUnit p i))⁻¹ 1 * complexMinus p K

def thetaVector (i : Fin ((p - 1) / 2)) : ComplexRing p K :=
  coeffCast p K (θminus p K (i.val + 1))

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma coeffCast_coeff (T : R p K) (g : G p K) :
    (coeffCast p K T).coeff g = (T.coeff g : ℂ) := rfl

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma coeffCast_single (g : G p K) (a : ℤ) :
    coeffCast p K (MonoidAlgebra.single g a) = MonoidAlgebra.single g (a : ℂ) := by
  exact MonoidAlgebra.mapRingHom_single _ _ _

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma coeffCast_injective : Function.Injective (coeffCast p K) := by
  intro A B h
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  have he := congrArg (fun T : ComplexRing p K => T.coeff g) h
  simp only [coeffCast_coeff] at he
  exact_mod_cast he

end Catalan.MinusIndependence
