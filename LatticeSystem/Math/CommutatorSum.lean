/-
Model-agnostic ring lemmas for distributing a commutator over a `Finset` sum, and their
scalar-weighted companions.

Placeholder for PR-2 of the §3.4 backfill arc: `commutator_sum_right`, `commutator_sum_left`,
`commutator_sum_smul_right`, `commutator_sum_smul_left` land here (design
`.self-local/reports/design-pr2-eq3411.md` §2, new file A). This module currently carries no
declarations; it exists so that `LocalDoubleCommutatorBound.lean` and the Tests fixtures that
import it resolve at the module level while the declarations themselves are still Red.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
