/-
Aggregator for the Anderson tower energy-bound development (Tasaki §4.2.1 Theorem 4.6).

This module re-exports the entire `AndersonTowerEnergyBound*` tree — the purely finite-volume
variational estimate proving Theorem 4.6 given the long-range-order hypothesis `q₀`:
the `U(1)`-symmetric order-operator `p̂` foundations and moment monotonicity (`…Phat`), the `SU(2)`
covariance of the order operators together with the passage to `⟨p̂⟩ ≥ 2 q₀` (`…SU2`), the
order-word sector structure and swap-telescoping estimates (`…SectorWords`), and the swap-chain
R1 induction with the tower denominator lower bound (`…R1`).  Downstream files import this single
module instead of the individual layers.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundPhat
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSU2
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundR1
