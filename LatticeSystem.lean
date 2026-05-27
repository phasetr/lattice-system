import LatticeSystem.Math.PerronFrobeniusPrimitive
import LatticeSystem.Math.CollatzWielandt
import LatticeSystem.Math.PerronFrobeniusMain
import LatticeSystem.Math.PerronFrobeniusSimple
import LatticeSystem.Math.PerronFrobeniusFinrank
import LatticeSystem.Math.PerronFrobenius
import LatticeSystem.Lattice.Graph
import LatticeSystem.Lattice.Scale
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.SpinHalfDecomp
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation
import LatticeSystem.Quantum.TimeReversalSpinHalf
import LatticeSystem.Quantum.TimeReversalMulti
import LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance
import LatticeSystem.Quantum.TimeReversalMulti.Heisenberg
import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.SU2Integral
import LatticeSystem.Quantum.SpinOne
import LatticeSystem.Quantum.SpinOneBasis
import LatticeSystem.Quantum.SpinOneDecomp
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.TotalSpin.Casimir
import LatticeSystem.Quantum.TotalSpin.Rotation
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.Rotation3D
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Quantum.GibbsState.Covariance
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.HeisenbergChain.Eigenvalues
import LatticeSystem.Quantum.HeisenbergChain.Gibbs
import LatticeSystem.Quantum.HeisenbergLattice
import LatticeSystem.Quantum.HeisenbergLattice.Companions
import LatticeSystem.Quantum.NeelState
import LatticeSystem.Quantum.MarshallDressedBasis
import LatticeSystem.Quantum.MarshallLiebMattis.Realness
import LatticeSystem.Quantum.MarshallLiebMattis.MarshallSignTrick
import LatticeSystem.Quantum.MarshallLiebMattis.Connectivity
import LatticeSystem.Quantum.MarshallLiebMattis.H0Matrix
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetization
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable
import LatticeSystem.Quantum.MarshallLiebMattis.H0Shifted
import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotSwapEntry
import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapEntry
import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotOffBond
import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapValue
import LatticeSystem.Quantum.MarshallLiebMattis.DressedSwapValue
import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedSwap
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowPath
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowExtend
import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedReachable
import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedIrreducible
import LatticeSystem.Quantum.MarshallLiebMattis.H0PFApplication
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian
import LatticeSystem.Quantum.MarshallLiebMattis.BipartiteGraph
import LatticeSystem.Quantum.MarshallLiebMattis.ToyPF
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin
import LatticeSystem.Quantum.Z2Z2
import LatticeSystem.Quantum.IsingChain
import LatticeSystem.Fermion.Mode
import LatticeSystem.Fermion.SingleMode
import LatticeSystem.Fermion.JordanWigner
import LatticeSystem.Fermion.JWAbstract
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
import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence
import LatticeSystem.Quantum.SpinS.Theorem23PFLadderLink
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancy
import LatticeSystem.Quantum.SpinS.Theorem23PFTotalSpin
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirEigenvector
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted
import LatticeSystem.Quantum.SpinS.Theorem23PFToyJointCasimir
import LatticeSystem.Quantum.SpinS.MagEigenvalueBound
import LatticeSystem.Quantum.SpinS.SublatticeSzBound
import LatticeSystem.Quantum.SpinS.CasimirWeightComponent
import LatticeSystem.Quantum.SpinS.CasimirSpectralBound
import LatticeSystem.Quantum.SpinS.SublatticeHighestWeight
import LatticeSystem.Quantum.SpinS.SublatticeLowestWeight
import LatticeSystem.Quantum.SpinS.Theorem23AntialignedJointEigenvector
import LatticeSystem.Quantum.SpinS.SublatticeMagnetization
import LatticeSystem.Quantum.SpinS.SublatticeMagShift
import LatticeSystem.Quantum.SpinS.SublatticeMagSpectrum
import LatticeSystem.Quantum.SpinS.SublatticeCasimirHighestWeightBound
import LatticeSystem.Quantum.SpinS.SublatticeMagProjection
import LatticeSystem.Quantum.SpinS.SublatticeMagWeightComponent
import LatticeSystem.Quantum.SpinS.SublatticeHighestWeightExistence
import LatticeSystem.Quantum.SpinS.SublatticeCasimirSpectralBound
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.CasimirSpectralLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyCasimirPin
import LatticeSystem.Quantum.SpinS.Theorem23ToySublatticeBounds
import LatticeSystem.Quantum.SpinS.Theorem23ExtremalSector
import LatticeSystem.Quantum.SpinS.Theorem23ExtremalHighestWeight
import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceLadderInvariant
import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceMagInvariant
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceNeBot
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceComplementNeBot
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceLadderInvariant
import LatticeSystem.Quantum.SpinS.SublatticeLadderIterate
import LatticeSystem.Quantum.SpinS.JointLadderIterate
import LatticeSystem.Quantum.SpinS.JointLadderIterateMag
import LatticeSystem.Quantum.SpinS.JointLadderIterateSublatticeMag
import LatticeSystem.Quantum.SpinS.JointLadderRaiseA
import LatticeSystem.Quantum.SpinS.JointLadderRaiseB
import LatticeSystem.Quantum.SpinS.JointLadderIterateNonvanishing
import LatticeSystem.Quantum.SpinS.JointDiagonalLI
import LatticeSystem.Quantum.SpinS.JointLadderRaiseBoundary
import LatticeSystem.Quantum.SpinS.JointDiagonalRaiseImage
import LatticeSystem.Quantum.SpinS.JointDiagonalKernel
import LatticeSystem.Quantum.SpinS.JointDiagonalPredictedEigenvector
import LatticeSystem.Quantum.SpinS.JointPredictedSectorEigenvector
import LatticeSystem.Quantum.SpinS.Theorem23ToyWitnessPredicted
import LatticeSystem.Quantum.SpinS.Theorem23PFBaseCasimir
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancyCasimir
import LatticeSystem.Quantum.SpinS.Theorem23JointPredictedLowering
import LatticeSystem.Quantum.SpinS.Theorem23JointPredictedSectors
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyArith
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeCasimirSzBound
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeLowestWeightSign
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeMagProjInfra
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeBottomComponent
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeMagBoundOneSide
import LatticeSystem.Quantum.SpinS.Theorem23TotalLowestWeightExistence
import LatticeSystem.Quantum.SpinS.Theorem23CoupledLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeCasimirNonneg
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyArithEq
import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimir
import LatticeSystem.Quantum.SpinS.Theorem23PredictedEnergySectorAll
import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimirAt
import LatticeSystem.Quantum.SpinS.Theorem23PFSectorCasimir
import LatticeSystem.Quantum.SpinS.Theorem23IntervalCommonEnergy
import LatticeSystem.Quantum.SpinS.Theorem23GlobalMinimality
import LatticeSystem.Quantum.SpinS.Theorem23ToySectorEnergyLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyFinal
import LatticeSystem.Quantum.SpinS.Theorem23TotalLoweringNonvanishing
import LatticeSystem.Quantum.SpinS.Theorem23GeneralHOutside
import LatticeSystem.Quantum.SpinS.Theorem23GeneralFinal
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.ManyBodyTensorS
import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import LatticeSystem.Quantum.SpinS.AxisSwapGaugeEquiv
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import LatticeSystem.Quantum.SpinS.SpinSTransverseLadder
import LatticeSystem.Quantum.SpinS.TwoSiteTransverseLadder
import LatticeSystem.Quantum.SpinS.SpinSReversal
import LatticeSystem.Quantum.SpinS.ManyBodyReversalS
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionSymmetry
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank
import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySpinHalf
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionEigenspace
import LatticeSystem.Quantum.SpinS.AxisSwapLadderForm
import LatticeSystem.Quantum.SpinS.AxisSwapLadderMagShift
import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.AxisSwapLadderEntry
import LatticeSystem.Quantum.SpinS.DressedBipartiteSign
import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag
import LatticeSystem.Quantum.SpinS.AxisSwapBondReNonneg
import LatticeSystem.Quantum.SpinS.AxisSwapBondVanish
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondSign
import LatticeSystem.Quantum.SpinS.SingleIonOffDiag
import LatticeSystem.Quantum.SpinS.DressedSingleIonSign
import LatticeSystem.Quantum.SpinS.DressedAxisSwapOffDiag
import LatticeSystem.Quantum.SpinS.AxisSwapBondParity
import LatticeSystem.Quantum.SpinS.AxisSwapParityBlock
import LatticeSystem.Quantum.SpinS.MagParityOperator
import LatticeSystem.Quantum.SpinS.MagParityEigenspaceDecomp
import LatticeSystem.Quantum.SpinS.DressedAxisSwapHermitian
import LatticeSystem.Quantum.SpinS.ParityDegeneracyBound
import LatticeSystem.Quantum.SpinS.ParityConfig
import LatticeSystem.Quantum.SpinS.DressedParityBlockMatrix
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateMag
import LatticeSystem.Quantum.SpinS.SublatticeLadderIdentity
import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateNonvanishing
import LatticeSystem.Quantum.SpinS.SublatticeLadderLI
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirFinrankGe
import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirFinrankGeComplement
import LatticeSystem.Quantum.SpinS.Theorem23ToyWitness
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound

/-!
# `lattice-system` library root

Top-level aggregator for the `lattice-system` Lean 4 + mathlib
library. Importing this file pulls in every public source module
(but not the `Tests/` regression-test modules — those live in
`LatticeSystem.Tests`, imported separately by the build).

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
