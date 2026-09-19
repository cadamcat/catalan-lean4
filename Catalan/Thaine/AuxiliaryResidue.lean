import Catalan.Thaine.AuxiliaryNormOne
import Catalan.Thaine.NormalizedResidue

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma auxiliary_normalized_unit_residue
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell) (a : (ZMod p)ˣ)
    (c : (𝓞 (A3.F p))ˣ)
    (hc : algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) =
      normalizedCircularValue p a (A3.primitiveRoot p))
    (eta : (𝓞 (A3.Bsub p ell))ˣ)
    (heta : algebraMap (A3.Bsub p ell) (mixedExtension p ell)
        ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) =
      normalizedPair p a (mixedPRoot p ell) (mixedEllRoot p ell))
    (P : Ideal (𝓞 (A3.Bsub p ell))) (hP : P.IsMaximal) (hellP : (ell : 𝓞 (A3.Bsub p ell)) ∈ P) :
    (eta : 𝓞 (A3.Bsub p ell)) -
      algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) ((c ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) ∈ P := by
  have auxiliaryResidueBaseMax : P.IsMaximal := hP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (mixedExtension p ell)) P
  have auxiliaryResidueTopMax : Q.IsMaximal := hQ
  have auxiliaryResidueLiesOver : Q.LiesOver P := hQP
  let k := 𝓞 (mixedExtension p ell) ⧸ Q
  let auxiliaryResidueField : Field k := Ideal.Quotient.field Q
  have hellQ : (ell : 𝓞 (mixedExtension p ell)) ∈ Q := by
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver Q P (ell : 𝓞 (A3.Bsub p ell))).mp hellP
  have hellzero : (ell : k) = 0 := by
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hellQ)
  have auxiliaryResidueChar : CharP k ell :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : ell.Prime)).mpr hellzero
  let uE : (𝓞 (mixedExtension p ell))ˣ :=
    Units.map (algebraMap (𝓞 (A3.Bsub p ell)) (𝓞 (mixedExtension p ell))).toMonoidHom eta
  let cE : (𝓞 (mixedExtension p ell))ˣ :=
    Units.map (algebraMap (𝓞 (A3.F p)) (𝓞 (mixedExtension p ell))).toMonoidHom c
  have huE : ((uE : 𝓞 (mixedExtension p ell)) : mixedExtension p ell) =
      normalizedPair p a (mixedPRoot p ell) (mixedEllRoot p ell) := heta
  have hcE : ((cE : 𝓞 (mixedExtension p ell)) : mixedExtension p ell) =
      normalizedCircularValue p a (mixedPRoot p ell) := by
    apply (algebraMap (mixedExtension p ell) A3.Omega).injective
    change algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) = _
    rw [hc]
    simp only [normalizedCircularValue, normalizedEpsilon_map, map_one]
    rfl
  have hz : IsPrimitiveRoot (mixedPRoot p ell) p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec p (Fact.out : p.Prime).pos
  have hwB : IsPrimitiveRoot (auxiliaryRoot p ell) ell := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos
  have hw : IsPrimitiveRoot (mixedEllRoot p ell) ell :=
    hwB.map_of_injective (algebraMap (A3.Bsub p ell) (mixedExtension p ell)).injective
  have hres := normalized_pair_residue (mixedExtension p ell) k p ell hpe
    (Ideal.Quotient.mk Q) (mixedPRoot p ell) (mixedEllRoot p ell) hz hw a uE cE huE hcE
  have hdiff : (uE : 𝓞 (mixedExtension p ell)) - (cE : 𝓞 (mixedExtension p ell)) ^ 2 ∈ Q := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_pow, hres, sub_self]
  change algebraMap (𝓞 (A3.Bsub p ell)) (𝓞 (mixedExtension p ell)) (eta : 𝓞 (A3.Bsub p ell)) -
    (algebraMap (𝓞 (A3.F p)) (𝓞 (mixedExtension p ell)) (c : 𝓞 (A3.F p))) ^ 2 ∈ Q at hdiff
  apply (Ideal.mem_of_liesOver Q P _).mpr
  simpa only [map_sub, Units.val_pow_eq_pow_val, map_pow,
    ← IsScalarTower.algebraMap_apply (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) (𝓞 (mixedExtension p ell))]
    using hdiff

lemma exists_auxiliary_unit_for_generator
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p])) (a : (ZMod p)ˣ)
    (c : (𝓞 (A3.F p))ˣ)
    (hc : algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) =
      normalizedCircularValue p a (A3.primitiveRoot p)) :
    ∃ eta : (𝓞 (A3.Bsub p ell))ˣ,
      Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 ∧
      ∀ P : Ideal (𝓞 (A3.Bsub p ell)), P.IsMaximal → (ell : 𝓞 (A3.Bsub p ell)) ∈ P →
        (eta : 𝓞 (A3.Bsub p ell)) -
          algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p ell)) ((c ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) ∈ P := by
  obtain ⟨eta, heta, hnorm⟩ := exists_auxiliary_norm_one_unit p ell hp2 hpe hell a
  exact ⟨eta, hnorm, fun P hP hellP =>
    auxiliary_normalized_unit_residue p ell hpe a c hc eta heta P hP hellP⟩

end Catalan.Thaine
