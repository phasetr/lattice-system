import LatticeSystem.Quantum.HorschVonderLindenTrialState
import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound

/-!
# The two-sided energy bound for the Horsch–von der Linden trial state (Tasaki eq. (3.4.12))

Placeholder module for the two declarations that will assemble Tasaki's printed two-sided bound

`0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS ≤ 8 d h₀ (o₀)² / (q₀ L^d)` (eq. (3.4.12), p. 67)

out of the basic variational estimate `hvlTrialState_energy_sub_eq` (eq. (3.4.8),
`HorschVonderLindenTrialState.lean`) and the locality numerator bound
`doubleCommutator_bondLocal_expectation_le` (eq. (3.4.11), `LocalDoubleCommutatorBound.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.3), (3.4.8), (3.4.11)–(3.4.12), pp. 65–67.
-/

namespace LatticeSystem.Quantum

open Matrix

end LatticeSystem.Quantum
