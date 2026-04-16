/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.SpinOneBasis

/-!
# Z₂ × Z₂ representations (Tasaki §2.1 eqs. (2.1.27)-(2.1.34))

The π-rotation operators `û_1, û_2, û_3` (both for S = 1/2 and S = 1)
form representations of the Klein four-group `Z₂ × Z₂`. This module
collects the abstract group relations.

## S = 1/2 (projective representation, eq. (2.1.31))

For half-odd-integer spin, `(û_α)² = -1` and `û_α û_β + û_β û_α = 0`,
giving a *projective* representation of `Z₂ × Z₂` — these are already
proved in `SpinHalfRotation.lean` as:
- `spinHalfRot{1,2,3}_pi_sq`
- `spinHalfRot{1,2,3}_pi_anticomm_*`
- `spinHalfRot{1,2,3}_pi_mul_*`

## S = 1 (genuine representation, eq. (2.1.27))

For integer spin, `(û_α)² = 1` and `û_α û_β = û_β û_α`, giving a
genuine (non-projective) representation — proved in
`SpinOneBasis.lean` as:
- `spinOnePiRot{1,2,3}_sq`
- `spinOnePiRot{1,2,3}_comm_*`
-/

namespace LatticeSystem.Quantum

/-!
This file serves as documentation that the Z₂ × Z₂ representation
structure (Tasaki eqs. (2.1.27)-(2.1.34)) is complete, split across
`SpinHalfRotation.lean` (S = 1/2, projective) and
`SpinOneBasis.lean` (S = 1, genuine).
-/

end LatticeSystem.Quantum
