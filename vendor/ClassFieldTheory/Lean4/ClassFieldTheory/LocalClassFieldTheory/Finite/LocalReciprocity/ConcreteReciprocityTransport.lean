/-
MODIFIED FROM UPSTREAM:
n-yamaguchi-0729/ClassFieldTheory commit 7713795234690681b4406ae198b07aa95e82716a.
Added Lean module-system visibility declarations and ported this file to Mathlib/Lean v4.35.0-rc3. Replaced private aliases with descriptive public names for downstream module use.
-/
module

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import Mathlib.FieldTheory.Galois.Basic
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm


/-!
# `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: transport of abstract reciprocity to a field extension

This file contains the final comparison step in the proof of the local
reciprocity law.  Once the actual absolute-Galois datum, henselian valuation,
and class-field axiom have been constructed, the abstract reciprocity theorem is transported
through the concrete finite Galois realization in a separable closure and
through the actual field norm.

The coefficient module remains `(SeparableClosure K)ˣ`; this is essential in
imperfect positive characteristic.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev concreteAbsoluteGaloisGroup (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev concreteAbsoluteUnitsRepresentation (K : Type) [Field K] : Rep ℤ (concreteAbsoluteGaloisGroup K) :=
  intrinsicAbsoluteUnits K

abbrev concreteAbstractBaseField (K : Type) [Field K] : ClosedSubgroup (concreteAbsoluteGaloisGroup K) :=
  intrinsicAbstractBase K

noncomputable instance intrinsicAbsoluteGaloisT2 : T2Space (concreteAbsoluteGaloisGroup K) :=
  krullTopology_t2

/-! ## Transport relative to an explicit embedding -/

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure. -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) : FiniteGaloisSubextension (concreteAbstractBaseField K) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
  below := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  normal := inferInstance
  finite := baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The concrete realization of `L/K` as the finite Galois extension object
to which the abstract reciprocity theorem is applied. -/
def finiteGaloisAbstractExtension : FiniteGaloisSubextension (concreteAbstractBaseField K) :=
  finiteGaloisAbstractExtensionOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The additive reciprocity equivalence transported through an explicit
realization of `L/K` in the separable closure. -/
def concreteReciprocityAddEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
  (MulEquiv.toAdditive
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr.symm)).trans
    ((D.abstractReciprocityEquiv (concreteAbsoluteUnitsRepresentation K) v hcf (intrinsicFiniteAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i)).trans
        (finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i))

/-- Multiplicative form of reciprocity transported through an explicit
embedding. -/
def concreteReciprocityEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L := by
  let e : Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf
  let em : Multiplicative (Additive (Abelianization Gal(L / K))) ≃*
      Multiplicative (Additive (NormQuotient K L)) :=
    @AddEquiv.toMultiplicative
      (Additive (Abelianization Gal(L / K)))
      (Additive (NormQuotient K L)) inferInstance inferInstance e
  exact (MulEquiv.multiplicativeAdditive
      (Abelianization Gal(L / K))).symm.trans
    (em.trans
        (MulEquiv.multiplicativeAdditive (NormQuotient K L)))

/-- Norm-residue symbol obtained from an explicit separable-closure
realization. -/
def concreteNormResidueSymbolOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Kˣ →* Abelianization Gal(L / K) :=
  (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm.toMonoidHom.comp
    (normClass K L)

/-- The additive form of the concrete reciprocity isomorphism.  The inputs
are the three genuine structures constructed in the preceding part of the
proof, not additional reciprocity hypotheses. -/
def concreteReciprocityAddEquiv
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
  concreteReciprocityAddEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf

/-- The public multiplicative form of the transported reciprocity
isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}Lˣ`. -/
def concreteReciprocityEquiv
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf

/-- The local norm-residue symbol obtained by inverting reciprocity and
precomposing with the quotient map on `Kˣ`. -/
def concreteNormResidueSymbol
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Kˣ →* Abelianization Gal(L / K) :=
  concreteNormResidueSymbolOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf

/-- The local norm-residue symbol is onto. -/
theorem concreteNormResidueSymbol_surjective
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    Function.Surjective (concreteNormResidueSymbol K L D v hcf) :=
  (concreteReciprocityEquiv K L D v hcf).symm.surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- The kernel of the local norm-residue symbol is exactly the field norm
subgroup. -/
theorem concreteNormResidueSymbol_ker
    (D : DegreeData (concreteAbsoluteGaloisGroup K)) (v : ValuationData D (concreteAbsoluteUnitsRepresentation K))
    (hcf : SatisfiesClassFieldAxiom (concreteAbsoluteUnitsRepresentation K)) :
    (concreteNormResidueSymbol K L D v hcf).ker = localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    (concreteReciprocityEquiv K L D v hcf).symm
        (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  constructor
  · intro hx
    have hx' := congrArg (concreteReciprocityEquiv K L D v hcf) hx
    rw [(concreteReciprocityEquiv K L D v hcf).apply_symm_apply,
      map_one] at hx'
    exact (normClass_eq_one_iff_mem K L x).1 hx'
  · intro hx
    have hq : normClass K L x = 1 :=
      (normClass_eq_one_iff_mem K L x).2 hx
    rw [hq, map_one]

end
end LocalClassFieldTheory
