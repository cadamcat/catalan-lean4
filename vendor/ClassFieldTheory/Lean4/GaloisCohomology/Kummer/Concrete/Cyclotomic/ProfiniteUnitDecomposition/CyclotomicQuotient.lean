import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk

set_option autoImplicit false

/-!
# The cyclotomic profinite-unit torsion quotient
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- Cyclotomic-character form of the torsion decomposition: quotienting `ℤ̂ˣ` by
the closure of its torsion subgroup leaves one copy of `ℤ̂`. -/
noncomputable def zHatUnitsTorsionQuotientEquiv :
    ZHatˣ ⧸ (CommGroup.torsion ZHatˣ).topologicalClosure ≃ₜ*
      Multiplicative ZHat :=
  torsionQuotientEquivOfZHatMulDecomposition
    ZHatˣ CyclotomicFinitePart
      zHatUnitsDecomposition
        dense_torsion_cyclotomicFinitePart

end KummerTheory
