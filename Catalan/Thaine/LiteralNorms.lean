module

public import Catalan.Thaine.LiteralMaps
public import Catalan.Wieferich.Defs

/-!
# `Catalan.Thaine.LiteralNorms`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance normMapsCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

def literalFieldUnitMap (p : ℕ) : (A3.F p)ˣ →* (A3.Bsub p p)ˣ :=
  Units.map (algebraMap (A3.F p) (A3.Bsub p p)).toMonoidHom

def literalNormMap (p : ℕ) : (A3.Bsub p p)ˣ →* (A3.F p)ˣ :=
  Units.map (Algebra.norm (A3.F p))

lemma literalNormMap_apply (p : ℕ) (x : (A3.Bsub p p)ˣ) :
    ((literalNormMap p x : (A3.F p)ˣ) : A3.F p) =
      Algebra.norm (A3.F p) (x : A3.Bsub p p) := rfl

def literalLambdaNorm (p : ℕ) [Fact p.Prime] (x : ℤ) (hp2 : p ≠ 2) : (A3.F p)ˣ :=
  literalNormMap p (A1e.lambdaUnit p (A3.Bsub p p) x hp2)

lemma literalLambdaNorm_apply
    (p : ℕ) [Fact p.Prime] (x : ℤ) (hp2 : p ≠ 2) :
    ((literalLambdaNorm p x hp2 : (A3.F p)ˣ) : A3.F p) =
      Algebra.norm (A3.F p)
        (((x : A3.Bsub p p) - ζ p (A3.Bsub p p)) / (1 - ζ p (A3.Bsub p p))) := rfl

end Catalan.Thaine
