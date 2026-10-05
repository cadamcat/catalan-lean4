module

public import Catalan.Thaine.AuxiliaryResidue
public import Catalan.Thaine.RealCircularUnit

/-!
# `Catalan.Thaine.CircularClosure`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def realCircularUnits (p : ℕ) : Subgroup (𝓞 (A3.F p))ˣ :=
  Subgroup.closure {u | u = -1 ∨ ∃ a : (ZMod p)ˣ,
    algebraMap (A3.F p) A3.Omega ((u : 𝓞 (A3.F p)) : A3.F p) =
      normalizedCircularValue p a (A3.primitiveRoot p)}

lemma exists_real_circular_generator
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    ∃ c : (𝓞 (A3.F p))ˣ, c ∈ realCircularUnits p ∧
      algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) =
        normalizedCircularValue p a (A3.primitiveRoot p) := by
  obtain ⟨c, hc⟩ := exists_real_circular_unit p hp2 a
  exact ⟨c, Subgroup.subset_closure (Or.inr ⟨a, hc⟩), hc⟩

private lemma quotient_units_eq_iff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : Ideal S) (u : Sˣ) (v : Rˣ) :
    Units.map (Ideal.Quotient.mk P).toMonoidHom u =
      Units.map ((Ideal.Quotient.mk P).comp f).toMonoidHom v ↔
      (u : S) - f (v : R) ∈ P := by
  rw [Units.ext_iff]
  change Ideal.Quotient.mk P (u : S) = Ideal.Quotient.mk P (f (v : R)) ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

lemma auxiliary_norm_unit
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p) :
    ∃ eta : (𝓞 (A3.Bsub p ell))ˣ,
      Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 ∧
      ∀ P : Ideal (𝓞 (A3.Bsub p ell)), P.IsMaximal → (ell : 𝓞 (A3.Bsub p ell)) ∈ P →
        (eta : 𝓞 (A3.Bsub p ell)) -
          algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) ∈ P := by
  let S : Subgroup (𝓞 (A3.F p))ˣ :=
    { carrier := {d | ∃ eta : (𝓞 (A3.Bsub p ell))ˣ,
        Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 ∧
        ∀ P : Ideal (𝓞 (A3.Bsub p ell)), P.IsMaximal → (ell : 𝓞 (A3.Bsub p ell)) ∈ P →
          Units.map (Ideal.Quotient.mk P).toMonoidHom eta =
            Units.map ((Ideal.Quotient.mk P).comp
              (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)))).toMonoidHom (d ^ 2)}
      one_mem' := by
        refine ⟨1, by simp, ?_⟩
        intro P hP hellP
        simp
      mul_mem' := by
        rintro a b ⟨eta, heta, ha⟩ ⟨theta, htheta, hb⟩
        refine ⟨eta * theta, ?_, ?_⟩
        · change Algebra.norm (A3.F p)
            (((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) *
              ((theta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell)) = 1
          rw [map_mul, heta, htheta, one_mul]
        · intro P hP hellP
          simpa only [map_mul, mul_pow] using congrArg₂ (· * ·) (ha P hP hellP) (hb P hP hellP)
      inv_mem' := by
        rintro a ⟨eta, heta, ha⟩
        refine ⟨eta⁻¹, ?_, ?_⟩
        · change Algebra.norm (A3.F p)
            (algebraMap (𝓞 (A3.Bsub p ell)) (A3.Bsub p ell)
              ((eta⁻¹ : (𝓞 (A3.Bsub p ell))ˣ) : 𝓞 (A3.Bsub p ell))) = 1
          simp only [map_units_inv, Algebra.norm_inv, heta, inv_one]
        · intro P hP hellP
          simpa only [map_inv, inv_pow] using congrArg Inv.inv (ha P hP hellP) }
  have hle : realCircularUnits p ≤ S := by
    apply (Subgroup.closure_le S).2
    intro c hc
    rcases hc with rfl | ⟨a, ha⟩
    · refine ⟨1, by simp, ?_⟩
      intro P hP hellP
      simp
    · obtain ⟨eta, heta, hres⟩ := exists_auxiliary_unit_for_generator p ell hp2 hpe hell a c ha
      refine ⟨eta, heta, ?_⟩
      intro P hP hellP
      exact (quotient_units_eq_iff
        (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell))) P eta (c ^ 2)).mpr (hres P hP hellP)
  obtain ⟨eta, heta, hres⟩ := hle hd
  refine ⟨eta, heta, ?_⟩
  intro P hP hellP
  exact (quotient_units_eq_iff
    (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell))) P eta (d ^ 2)).mp (hres P hP hellP)

end Catalan.Thaine
