import LatticeSystem.Math.GramEigenspaceCorrespondence
import LatticeSystem.Math.RayleighAtEigenvector
import LatticeSystem.Math.RealEigenvalueLePF
import LatticeSystem.Math.EffectiveLimit
import LatticeSystem.Math.MatrixAnalysis.Decomposition
import LatticeSystem.Math.WignerTheorem
import LatticeSystem.Math.CStarAlgebra.GNS
import LatticeSystem.Quantum.HorschVonderLinden
import LatticeSystem.Quantum.KaplanHorschVonderLinden
import LatticeSystem.Quantum.SpinS.FalkBruchInfra
import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D
import LatticeSystem.Quantum.SpinS.MPSTheorem75
import LatticeSystem.Quantum.SpinS.AKLTMatrixProduct
import LatticeSystem.Quantum.SpinS.AKLTInfiniteChain
import LatticeSystem.Quantum.SpinS.AKLTStringOrder
import LatticeSystem.Quantum.SpinS.AKLTTheorem71
import LatticeSystem.Quantum.SpinS.ClusterState
import LatticeSystem.Quantum.SpinS.HoneycombAKLTZeroEnergy
import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrderUniqueness
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGap
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneralDischarge
import LatticeSystem.Quantum.SpinS.RingReflection
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareSusceptibilitySumRule
import LatticeSystem.Quantum.SpinS.RingReflectionChessboardTransport
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMomentRatio
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereGroundState
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentAssembly
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateTower
import LatticeSystem.Quantum.SpinS.HypercubicBoxThermodynamicLimit
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem411
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem413
import LatticeSystem.Quantum.SpinS.AndersonTowerEigenstates
import LatticeSystem.Quantum.SpinS.QuasiLocalRealization
import LatticeSystem.Quantum.SpinS.MarshallLiebMattisSectorBundled
import LatticeSystem.Quantum.SpinS.SectorFinrankTransfer
import LatticeSystem.Quantum.SpinS.Theorem24SU2SymmetricFinrankLeOneCardEq
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIStrictGapBridge
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIICrossingSetFromFirst
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTheorem24
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfCaseII
import LatticeSystem.Quantum.SpinS.MultiSiteCasimir
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianConcreteClusters
import LatticeSystem.Quantum.SpinS.GraphLocalStarSumWrapper
import LatticeSystem.Quantum.SpinS.Problem25cBalancedStructuralWrapper
import LatticeSystem.Quantum.SpinS.SingleSiteXYExpectation
import LatticeSystem.Quantum.SpinS.Lagrange
import LatticeSystem.Quantum.SpinS.LadderRecursion
import LatticeSystem.Quantum.SpinS.DiagProjProperties
import LatticeSystem.Quantum.SpinS.Eigenstates
import LatticeSystem.Quantum.SpinS.LadderStates
import LatticeSystem.Quantum.SpinS.CasimirEigenvalue
import LatticeSystem.Quantum.SpinS.CasimirInvariance
import LatticeSystem.Quantum.SpinS.DiagProjOrtho
import LatticeSystem.Quantum.SpinS.SpanningTheorem
import LatticeSystem.Lattice.Scale
import LatticeSystem.Quantum.SU2Integral
import LatticeSystem.Quantum.SpinOneDecomp
import LatticeSystem.Quantum.Rotation3D
import LatticeSystem.Quantum.HeisenbergChain.Gibbs
import LatticeSystem.Quantum.HeisenbergLattice.Companions
import LatticeSystem.Quantum.NeelState
import LatticeSystem.Quantum.MarshallLiebMattis.ToyPF
import LatticeSystem.Quantum.Z2Z2
import LatticeSystem.Fermion.SingleMode
import LatticeSystem.Fermion.JordanWigner.FockSpaceRepresentation
import LatticeSystem.Fermion.JordanWigner.SmearedCAR
-- Tasaki §2.5 Theorem 2.3 (spin-S Marshall–Lieb–Mattis) tree.
-- These are the in-progress final-wrapper "tip" modules; importing them here
-- pulls the whole §2.5 module tree into the build root so the default
-- `lake build` (and CI) elaborates it, rather than leaving it reachable only
-- via per-module builds.
-- Tasaki §2.5 Theorem 2.3: the saturated-ladder-iterate route was found unsound
-- (the `hdominates` leaf is false; the ferromagnetic ladder iterate is not the
-- Marshall-positive AFM ground state — see .self-local/docs/tasaki-2-5-pf-route-design.md).
-- The sound per-sector Perron–Frobenius ground state is kept; the unsound conditional
-- wrapper tree (40 modules) is removed.  Issue #3542.
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancy
import LatticeSystem.Quantum.SpinS.CasimirSpectralBound
import LatticeSystem.Quantum.SpinS.Theorem23AntialignedJointEigenvector
import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceLadderInvariant
import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceMagInvariant
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceComplementNeBot
import LatticeSystem.Quantum.SpinS.Theorem23PFBaseCasimir
import LatticeSystem.Quantum.SpinS.KennedyTasakiTransformation
import LatticeSystem.Quantum.SpinS.LambdaDModel
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisDiscrete
import LatticeSystem.Quantum.SpinS.SPTMatrixProductIndex
import LatticeSystem.Quantum.SpinS.SPTPhase
import LatticeSystem.Quantum.SpinS.SPTPhaseTransition
import LatticeSystem.Quantum.SpinS.SPTTopologicalIndex
import LatticeSystem.Quantum.SpinS.ToricCode
import LatticeSystem.Quantum.SpinS.AxisSwapLadderMagShift
import LatticeSystem.Quantum.SpinS.BareSubmatrixPFFinrank
import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFAtMin
import LatticeSystem.Quantum.SpinS.DressedSubmatrixBoundAtMin
import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversalFinal
import LatticeSystem.Quantum.SpinS.ParityReachConcentrateAB
import LatticeSystem.Quantum.SpinS.ParityReachCanonicalMagShift
import LatticeSystem.Quantum.SpinS.DressedParityBlockMatrix
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirFinrankGeComplement
import LatticeSystem.Quantum.SpinS.Problem25dGroundStatePhaseWrapper
import LatticeSystem.Quantum.SpinS.Problem25dBalancedPFCrossSign
import LatticeSystem.Quantum.SpinS.SpinHalfSpecializationMultiSite

/-!
# `lattice-system` library root

Top-level aggregator for the `lattice-system` Lean 4 + mathlib
library. Importing this file pulls in every public source module
(but not the `Tests/` regression-test modules — those live in
`LatticeSystem.Tests`, imported separately by the build).

The list above enumerates only the tips of the library's import
DAG — the modules that no other library module imports — because
everything else is reached transitively; a module needs a line
here exactly when nothing else in the library imports it.

The library's design philosophy is **graph-centric**: the
underlying combinatorial datum of every many-body system is a
graph `(Λ, E_Λ)` (concrete lattices like 1D chain / 2D square /
3D cubic / `ℤ^d` are graph instances), and finiteness is
required only locally where the matrix / trace / partition-
function machinery needs it.

For the formalisation status, the per-module breakdown, and the
mathematical references, see the project page:
<https://phasetr.github.io/lattice-system/>.
-/
