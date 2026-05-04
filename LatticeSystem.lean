import LatticeSystem.Math.PerronFrobeniusPrimitive
import LatticeSystem.Math.CollatzWielandt
import LatticeSystem.Math.PerronFrobeniusMain
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
