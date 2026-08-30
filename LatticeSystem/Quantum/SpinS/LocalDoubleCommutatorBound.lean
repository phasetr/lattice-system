/-
The locality core for Tasaki eqs. (3.4.9)-(3.4.11).

Placeholder for PR-2 of the §3.4 backfill arc: `commutator_orderSum_eq_windowSum` (3.4.9),
`doubleCommutator_orderSum_eq_windowSum` (3.4.10), the norm kernel
`manyBodyOperatorNormS_doubleCommutator_le_of_windows`, and the capstone
`doubleCommutator_bondLocal_expectation_le` (3.4.11) land here (design
`.self-local/reports/design-pr2-eq3411.md` §2-3, new file B). This module currently carries no
declarations; it exists so that the Tests fixtures importing it resolve at the module level while
the declarations themselves are still Red.
-/
import LatticeSystem.Math.CommutatorSum
import LatticeSystem.Quantum.SpinS.ExpectationNormBound
