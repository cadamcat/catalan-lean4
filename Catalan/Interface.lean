import Catalan.Cyclotomic.Basic
import Catalan.Cyclotomic.GroupRingMul
import Catalan.Cyclotomic.Augmentation
import Catalan.IdealHelpers
import Catalan.Cassels.LambdaIdeal
import Catalan.Density.Definitions
import Catalan.Cassels.Hyyro
import Catalan.Mihailescu.Ideal
import Catalan.Stickelberger.Reduction
import Catalan.Stickelberger.Away
import Catalan.Stickelberger.ResidueGauss
import Catalan.Stickelberger.GammaAssembly
import Catalan.Stickelberger.DigitValuation
import Catalan.Stickelberger.DigitResidue
import Catalan.Cyclotomic.OtherPrime
import Catalan.Mihailescu.Orders
import Catalan.Mihailescu.Separation
import Catalan.Stickelberger.NormalizedGauss
import Catalan.Stickelberger.LocalGauss
import Catalan.Stickelberger.SquareZeroSection
import Catalan.Stickelberger.Teichmuller
import Catalan.Stickelberger.SectionBridge
import Catalan.Stickelberger.WittTower
import Catalan.Stickelberger.TowerArith
import Catalan.Stickelberger.GaussFamily
import Catalan.Stickelberger.GaussIdentities
import Catalan.Stickelberger.ValuesBridge
import Catalan.Stickelberger.WittTower
import Catalan.Stickelberger.Tower
import Catalan.Stickelberger.Local
import Catalan.Stickelberger.Uniformizer
import Catalan.Stickelberger.Factor
import Catalan.FactorBridge
import Catalan.Stickelberger.Values
import Catalan.FactorDescent
import Catalan.Stickelberger.Transfer
import Catalan.Stickelberger.GaloisCover
import Catalan.Stickelberger.GaussGalois
import Catalan.Stickelberger.Descent
import Catalan.Stickelberger.RootDescent
import Catalan.Stickelberger.Equivariance
import Catalan.Stickelberger.Identify
import Catalan.Stickelberger.Annihilation

import Catalan.Mihailescu.PhaseBounds
import Catalan.Mihailescu.ExpBound
import Catalan.Mihailescu.Numerical
import Catalan.Classical.Reduction

import Catalan.Mihailescu.Threshold
import Catalan.Mihailescu.RealContradiction
import Catalan.Mihailescu.RootPhase
import Catalan.Mihailescu.RadiusTwoArithmetic

import Catalan.Mihailescu.FiniteSum

import Catalan.Wieferich.DoubleWieferich

import Catalan.Classical.Lebesgue
import Catalan.Classical.Euler
import Catalan.Classical.KoChao
import Catalan.Counting
import Catalan.CaseTwo.WeakBoundExclusion
import Catalan.Stickelberger.MinusStability
import Catalan.Stickelberger.MinusNorm
import Catalan.Stickelberger.MinusMihailescu
import Catalan.Stickelberger.MinusSpan
import Catalan.Stickelberger.CharacterZeroBridge
import Catalan.Stickelberger.CharacterBoundary
import Catalan.Stickelberger.CharacterSpecialValue
import Catalan.Stickelberger.MinusIndependent
import Catalan.Cyclotomic.GroupRingSums
import Catalan.Counting.ThetaCombination
import Catalan.Counting.CoefficientBall
import Catalan.Counting.QuotientBall
import Catalan.Counting.SmallBall
import Catalan.CaseTwo.LatticeWeak
import Catalan.CaseTwo.RadiusArithmetic
import Catalan.CaseTwo.HyyroThreshold
import Catalan.CaseTwo.HyyroCorollaryInputs
import Catalan.Height.Basic
import Catalan.Height.Projective
import Catalan.Height.Liouville
import Catalan.Height.LocalBounds
import Catalan.Mihailescu.PositiveProducts
import Catalan.Mihailescu.GroupRingHeight
import Catalan.Mihailescu.KernelCardinality
import Catalan.Mihailescu.ReconstructHeight
import Catalan.Mihailescu.RadiusTwoHeight
import Catalan.Mihailescu.RadiusTwoExclusion
import Catalan.Classical.SmallConductors
import Catalan.CaseTwo.WeakBounds
import Catalan.CaseTwo.Assembly
import Catalan.Density.BaseFields
import Catalan.CaseOne.SemisimpleIdeal
import Catalan.Density.FiniteM
import Catalan.Density.NormalM
import Catalan.CaseOne.PrimaryCongruence
import Catalan.CaseOne.PrimaryPolynomial
import Catalan.CaseOne.PowerBasisDivisibility
import Catalan.CaseOne.PrimaryObstruction
import Catalan.Density.RealF
import Catalan.Density.FStructure
import Catalan.CaseOne.RatioUnits
import Catalan.CaseOne.PrimaryUnits
import Catalan.CaseOne.PrimaryNaturality
import Catalan.CaseOne.CircularUnits
import Catalan.CaseOne.CircularStability
import Catalan.CaseOne.PowerQuotient
import Catalan.CaseOne.PowerImage
import Catalan.CaseOne.UnitRepresentation
import Catalan.CaseOne.CircularModule
import Catalan.CaseOne.FullLog
import Catalan.CaseOne.TorsionReduction
import Catalan.CaseOne.PowerModN
import Catalan.CaseOne.LatticeCharpoly
import Catalan.CaseOne.ModNAction
import Catalan.CaseOne.CMBridge
import Catalan.CaseOne.LogSpaceEquiv
import Catalan.CaseOne.IntegralRepresentation
import Catalan.CaseOne.Places
import Catalan.CaseOne.Regular
import Catalan.CaseOne.UnitCharpoly
import Catalan.CaseOne.CyclicShift
import Catalan.CaseOne.CyclicZeroSum
import Catalan.CaseOne.PlaceCycle
import Catalan.CaseOne.GeometricSquarefree
import Catalan.CaseOne.CyclotomicPlaces
import Catalan.CaseOne.PlaceCharpoly
import Catalan.CaseOne.CaseTwoCard
import Catalan.CaseOne.GeometricUnits
import Catalan.CaseOne.CyclicVector
import Catalan.CaseOne.RepresentationCyclic
import Catalan.CaseOne.UnitCyclic
import Catalan.CaseOne.MinpolyCyclic
import Catalan.CaseOne.GroupEvaluation
import Catalan.CaseOne.ProductAnn
import Catalan.CaseOne.RepresentationAnnihilator
import Catalan.CaseOne.GeneratorConjugation
import Catalan.CaseOne.Filtration
import Catalan.CaseOne.NormSum
import Catalan.CaseOne.NormIdeal
import Catalan.CaseOne.GaloisRing
import Catalan.CaseOne.ThreeStep
import Catalan.CaseOne.UnitNorm
import Catalan.CaseOne.UnitFiltration
import Catalan.CaseOne.AnnihilatorDuality
import Catalan.CaseOne.Involution
import Catalan.CaseOne.PlusAugmentation

import Catalan.CaseOne.RealTorsion
import Catalan.Density.Bdegree
import Catalan.CaseOne.DualCharpoly
import Catalan.CaseOne.ProjectiveRigidity
import Catalan.CaseOne.RealUnits
import Catalan.CaseOne.NormDescent
import Catalan.Density.FUnits
import Catalan.Density.UnitFieldInjection

import Catalan.Density.AbsoluteM
import Catalan.Density.RootRatio
import Catalan.Density.RootCoordinates
import Catalan.Density.UnitRoots
import Catalan.Density.UnitRootExt
import Catalan.Density.KummerTower
import Catalan.Density.PairingValues
import Catalan.Density.Faithful
import Catalan.Density.FixedRoot
import Catalan.Density.PairingDual
import Catalan.Density.DualLeft
import Catalan.Density.DualRight
import Catalan.Density.PerfectKummer
import Catalan.Density.AbsoluteB

import Catalan.Density.RootCoordinateAction
import Catalan.Density.ConjugateOver
import Catalan.Density.RootCharacter
import Catalan.Density.InertiaBridge
import Catalan.Density.AbsoluteAction
import Catalan.Density.InfiniteUnramified
import Catalan.Density.KummerCovariance
import Catalan.Density.ScalarFixed
import Catalan.Density.UnramifiedWitness
import Catalan.Density.BaseFixing
import Catalan.Density.MCentralizer
import Catalan.Density.HRelative

import Catalan.Density.TTower
import Catalan.Density.SupExt
import Catalan.Density.InertiaRestrictions
import Catalan.Density.DegreeBound
import Catalan.Density.UnramifiedSup
import Catalan.Density.BoundedSup
import Catalan.Density.TRelative
import Catalan.Density.FiniteH
import Catalan.Density.FiniteT
import Catalan.Density.TSelector
import Catalan.Density.HDisjoint

import Catalan.Density.FieldTransport
import Catalan.Density.ConjugateField
import Catalan.Density.ConjugateWitness
import Catalan.Density.AbsoluteH
import Catalan.Density.AbsoluteT
import Catalan.Density.CyclicCentralizer

import Catalan.Density.NativeFrobenius
import Catalan.Density.FrobeniusStabilizer
import Catalan.Density.FixedFieldPlaces
import Catalan.Density.FinitePlacePreservation
import Catalan.Density.RationalPlaces
import Catalan.Density.FrobeniusPower
import Catalan.Density.UnramifiedPreservedPrime
import Catalan.Density.DensityTheorem

import Catalan.Runge.Definitions
import Catalan.Runge.CoefficientIntegral
import Catalan.Runge.ErrorBound
import Catalan.Runge.CoeffResidue
import Catalan.Runge.SmallConjugates
import Catalan.Density.ClassGroupArtin
import Catalan.Density.PowerFixedField
import Catalan.Density.UnramifiedModel
import Catalan.Density.HClassQuotient

import Catalan.Runge.BinomialSeries

import Catalan.Density.ArtinIdele

import Catalan.Runge.ProductCoefficients
import Catalan.Runge.RootReality
import Catalan.Runge.ProductReality
import Catalan.Runge.CoefficientMajorant
import Catalan.Runge.ProductSeries
import Catalan.Runge.ApproximationMap
import Catalan.Runge.RootEvaluation
import Catalan.Runge.TailBound
import Catalan.Runge.Estimate
import Catalan.Runge.ReducedQuotient
import Catalan.Runge.CoefficientBasis
import Catalan.Runge.IntegralApproximation
import Catalan.Runge.Reduction
import Catalan.Runge.Normalized

import Catalan.Runge.Growth
import Catalan.Runge.PowerTransport
import Catalan.Runge.BoundedLift
import Catalan.Runge.PlusInputs
import Catalan.Runge.FullInjective
import Catalan.Runge.PlusIdeal
import Catalan.Density.CyclicKummerCentralizer

import Catalan.Density.GaloisModules
import Catalan.Density.SelectorLift
import Catalan.Density.SelectorConjugate
import Catalan.Density.HLift
import Catalan.Density.KummerConjugateSpan
import Catalan.Density.TConjugate
import Catalan.Density.HRestriction
import Catalan.Density.SelectorSpan
import Catalan.Density.ClassGroupLinear
import Catalan.Density.SelectorClassSpan

import Catalan.Density.PrimeArtinFormula
import Catalan.Density.PrimeArtinDecomposition
import Catalan.Density.FixedResidue
import Catalan.Density.FrobeniusRestrict
import Catalan.Density.RelativeFrobenius
import Catalan.Density.PrimeFrobenius
import Catalan.Density.HPrimeFrobenius
import Catalan.Density.SelectorPrimes

import Catalan.Density.ResidueMap
import Catalan.Density.CyclicSelectorFamily
import Catalan.Density.CyclicFunctional
import Catalan.Density.IntegralUnitRoot
import Catalan.Density.ResidueRoot
import Catalan.Density.ResiduePowerMap
import Catalan.Density.ResidueKernel
import Catalan.Density.CyclicPrimeClasses
import Catalan.Density.KummerResidue
import Catalan.Density.RootResidueCard
import Catalan.Density.UnitResidueInjective
import Catalan.Density.QPrimeCongruence
import Catalan.Density.SeparatingPrimeClasses

import Catalan.Density.RealPrimeCongruence
import Catalan.Density.ResidueCoordinate
import Catalan.Density.OrbitCoordinates
import Catalan.Density.FUnitAugmentation
import Catalan.Density.UnitResidueCoordinates
import Catalan.Density.AugmentationPrimeClasses
import Catalan.Thaine.Hilbert90

import Catalan.Thaine.IntegralUnitPow
import Catalan.Thaine.ResidueExponent
import Catalan.Density.OrbitAction
import Catalan.Thaine.RealModel
import Catalan.Thaine.AuxiliaryGenerator
import Catalan.Thaine.UnitResidueExponents
import Catalan.Thaine.AuxiliaryIntegralHilbert90
import Catalan.Thaine.MixedRootUnits
import Catalan.Thaine.MixedEpsilonUnit

import Catalan.Thaine.Normalization
import Catalan.Thaine.CyclotomicNorm
import Catalan.Thaine.MixedDescent
import Catalan.Thaine.IntegralUnitDescent
import Catalan.Thaine.EpsilonInversion
import Catalan.Thaine.NormFactor
import Catalan.Thaine.NormalizedPair
import Catalan.Thaine.CircularValueUnit
import Catalan.Thaine.MixedNormBase
import Catalan.Thaine.NormalizedNorm
import Catalan.Thaine.NormalizedResidue
import Catalan.Thaine.AuxiliaryNormOne
import Catalan.Thaine.RealCircularUnit
import Catalan.Thaine.AuxiliaryResidue
import Catalan.Thaine.CircularClosure
import Catalan.Thaine.AuxiliaryIntegerData

import Catalan.Thaine.RealUnramified
import Catalan.Thaine.PrimeUniformizer
import Catalan.Thaine.InvariantPrincipal
import Catalan.Thaine.CyclotomicAway
import Catalan.Thaine.TotalRamification
import Catalan.Thaine.AuxiliaryUniformizer
import Catalan.Thaine.TotalInertia
import Catalan.Thaine.LocalExponent
import Catalan.Thaine.AuxiliaryRamification
import Catalan.Thaine.ResidueExtension
import Catalan.Thaine.AuxiliaryResidueHom

import Catalan.Thaine.LocalAction
import Catalan.Thaine.LocalMultiplicity
import Catalan.Thaine.DvrDecomposition
import Catalan.Thaine.DedekindLocalExponent
import Catalan.Thaine.AuxiliaryLocalExponent
import Catalan.Thaine.CircularPrincipalData

import Catalan.Thaine.NormMultiplicity
import Catalan.Thaine.InvariantFiber
import Catalan.Thaine.ClassFactorization
import Catalan.Thaine.NormFibers
import Catalan.Thaine.PrincipalClassRelation
import Catalan.Thaine.AuxiliaryNormMultiplicities
import Catalan.Thaine.CircularClassRelation

import Catalan.Thaine.PrimeOrbit
import Catalan.Thaine.ConjugateResidue
import Catalan.Thaine.OrdinaryClassAction
import Catalan.Thaine.OrbitReindex
import Catalan.Thaine.ClassRepresentation
import Catalan.Thaine.ResidueCoordinateSquare
import Catalan.Thaine.CircularOrbitRelation
import Catalan.Thaine.CircularCoordinateAnnihilator

import Catalan.Thaine.PrimeNormProduct
import Catalan.Thaine.PrimeClassSpan
import Catalan.Thaine.CoordinateElement
import Catalan.Thaine.RealUnitAnnihilator
import Catalan.Thaine.ClassNorm
import Catalan.Thaine.ThainePrimeAnnihilator
import Catalan.Thaine.ThaineClassQuotient

import Catalan.Thaine.LiteralMaps
import Catalan.Thaine.CircularImageComparison
import Catalan.Thaine.LiteralPowerInjection
import Catalan.Thaine.LiteralRestrictionAction
import Catalan.Thaine.LiteralFullAnnihilator
import Catalan.Thaine.LiteralClassRepresentation
import Catalan.Thaine.LiteralAnnihilatorReflection
import Catalan.Thaine.LiteralFullThaine

import Catalan.Thaine.PrimaryNilpotence
import Catalan.Thaine.FrobeniusPower
import Catalan.Thaine.IntegralClassAction
import Catalan.Thaine.GroupRingStructure
import Catalan.Thaine.PrimaryGoodLift
import Catalan.Thaine.LiteralIntegerClassAction
import Catalan.Thaine.LiteralPrimaryLift

import Catalan.Thaine.LiteralNorms
import Catalan.Thaine.LiteralFieldPowers
import Catalan.Thaine.IdealClassPower
import Catalan.Thaine.LiteralQuadraticNorm
import Catalan.Thaine.LiteralClassUnitPower
import Catalan.Thaine.LiteralLambdaIdeal
import Catalan.Thaine.LiteralNormPowers
import Catalan.Thaine.LiteralLambdaPower

import Catalan.Thaine.CircularizePowers
import Catalan.Thaine.RawPiCircularPower
import Catalan.Thaine.SymmetrizedCongruence
import Catalan.Thaine.PlusAugmentationLift
import Catalan.Thaine.CircularPowerTransport
import Catalan.Thaine.LiteralCircularPower
import Catalan.Thaine.LiteralRootCircularPower

import Catalan.Thaine.PrimaryLocalization
import Catalan.Thaine.UnitPowerReflection
import Catalan.Thaine.BottomPower
import Catalan.Thaine.LocalizedPrimaryCriterion
import Catalan.Thaine.PrimaryLocalizedPowers
import Catalan.Thaine.IdealNonzero
import Catalan.Thaine.PrimaryUpow
import Catalan.Thaine.LiteralPrimaryPower
import Catalan.Thaine.LiteralPurePower
import Catalan.Thaine.PrimeAssemblyReduction
import Catalan.Thaine.NaturalClassificationReduction
import Catalan.Thaine.LiteralRungeContradiction
import Catalan.Final.Assembly
import Catalan.Final.Signed

/-! Proved statements exported by this module.

The cyclotomic setup, group-ring algebra, Cassels arithmetic and ideal powers,
Hyyrö's bound, the Mihăilescu ideal and the prime-selection input definitions are
available here. General Stickelberger annihilation is proved in `Stickelberger/Annihilation.lean`.
The original integer and natural Catalan theorems, odd-prime impossibility, and Case 1
are proved and exported through `Final/Assembly.lean`.
-/

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

/-- Compatibility of the unit action used by the shared and ideal interfaces. -/
lemma actUnit_eq_elementAct (τ : G p K) : actUnit p K τ = elementAct K τ := rfl

/-- Group-ring powers commute with passage from field units to principal ideals. -/
lemma ipow_principalIdeal_upow (γ : Kˣ) (Θ : R p K) :
    ipow p K (principalIdeal K γ) Θ = principalIdeal K (upow p K γ Θ) :=
  ipow_principalIdeal p K γ Θ

end Catalan
