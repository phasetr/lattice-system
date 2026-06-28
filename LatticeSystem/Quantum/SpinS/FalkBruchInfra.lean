/-
Aggregator for the Tasaki §4.1 Corollary 4.3 Falk–Bruch / f-sum-rule development.

This module re-exports the ground-state Falk–Bruch and f-sum-rule infrastructure used toward
Corollary 4.3 (absence of long-range order in one dimension):
the staggered order parameter squared as a two-point sum, the single-bond and Hamiltonian
spin-current commutators, the per-bond and order double commutators (the f-sum-rule oscillator
strength), the double-commutator = variational energy identity and its nonnegativity, the abstract
and concrete Falk–Bruch inequalities, and the positive-semidefiniteness of the ground-energy-shifted
Hamiltonian.  Downstream files (and the build root) import this single module, not the layers.
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderSquare
import LatticeSystem.Quantum.SpinS.StaggeredOrderSquareForm
import LatticeSystem.Quantum.SpinS.StaggeredOrderCommutator
import LatticeSystem.Quantum.SpinS.StaggeredOrderDoubleCommutator
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator
import LatticeSystem.Quantum.SpinS.HeisenbergSpinSOp3Commutator
import LatticeSystem.Quantum.SpinS.SingleBondDoubleCommutator
import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational
import LatticeSystem.Quantum.SpinS.DoubleCommutatorNonneg
import LatticeSystem.Quantum.SpinS.FalkBruch
import LatticeSystem.Quantum.SpinS.HermitianSubMinPosSemidef
import LatticeSystem.Quantum.SpinS.FalkBruchDoubleCommutator
