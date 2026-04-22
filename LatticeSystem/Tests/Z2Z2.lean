/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.Z2Z2
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.SpinOneBasis

/-!
# Test coverage for Quantum/Z2Z2

`Z2Z2.lean` is documentation-only: the actual Z₂ × Z₂ representation
relations live in `SpinHalfRotation.lean` (S = 1/2 projective) and
`SpinOneBasis.lean` (S = 1 genuine). These tests pin a representative
of each.

(Per refactor plan v4 §9 mapping table; refactor Phase 1 PR 13, #281.)
-/

namespace LatticeSystem.Tests.Z2Z2

open LatticeSystem.Quantum

/-! ## D. S = 1/2 projective: `(û_α)² = -1` (Tasaki (2.1.31)) -/

example : spinHalfRot1 Real.pi * spinHalfRot1 Real.pi = -1 :=
  spinHalfRot1_pi_sq

example : spinHalfRot2 Real.pi * spinHalfRot2 Real.pi = -1 :=
  spinHalfRot2_pi_sq

example : spinHalfRot3 Real.pi * spinHalfRot3 Real.pi = -1 :=
  spinHalfRot3_pi_sq

end LatticeSystem.Tests.Z2Z2
