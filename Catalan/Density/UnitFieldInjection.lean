module

public import Catalan.CaseOne.NormDescent
public import Catalan.CaseOne.PowerQuotient
public import Catalan.Density.Bdegree

/-!
# `Catalan.Density.UnitFieldInjection`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitQuotient
variable (F L : Type*) [Field F] [NumberField F] [Field L] [Algebra F L]

/-- The actual embedding of integral units into the larger field's units. -/
def unitFieldMap : (𝓞 F)ˣ →* Lˣ :=
  Units.map (((algebraMap F L).comp (algebraMap (𝓞 F) F)).toMonoidHom)

def unitFieldPowerMap (q : ℕ) : PowerQuotient (𝓞 F)ˣ q →ₗ[ZMod q]
    PowerQuotient Lˣ q := powerMap q (unitFieldMap F L)

lemma unitFieldPowerMap_injective [FiniteDimensional F L]
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q (Module.finrank F L)) :
    Function.Injective (unitFieldPowerMap F L q) := by
  apply (injective_iff_map_eq_zero (unitFieldPowerMap F L q)).mpr
  intro z hz
  induction z using QuotientGroup.induction_on with
  | _ u =>
    change (QuotientGroup.mk (unitFieldMap F L u) : Lˣ ⧸ qPowers Lˣ q) = 1 at hz
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff (unitFieldMap F L u)).mp hz
    have hroot : ∃ b : L, b ^ q = algebraMap F L ((u : 𝓞 F) : F) := by
      refine ⟨(b : L), ?_⟩
      exact congrArg Units.val hb
    obtain ⟨v, hv⟩ := unit_qth_root_of_field_qth_root F q hq u
      (field_qth_root_of_coprime_degree F L q hc _ hroot)
    change (QuotientGroup.mk u : (𝓞 F)ˣ ⧸ qPowers (𝓞 F)ˣ q) = 1
    exact (QuotientGroup.eq_one_iff u).mpr ⟨v, hv⟩

end Catalan.UnitQuotient
namespace Catalan.A3

lemma F_unit_powerMap_B_injective (p q : ℕ) (hq : q.Prime) :
    Function.Injective (UnitQuotient.unitFieldPowerMap (F p) (Bsub p q) q) :=
  UnitQuotient.unitFieldPowerMap_injective (F p) (Bsub p q) q hq.pos
    (coprime_q_finrank_B p q hq)

end Catalan.A3
