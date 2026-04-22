/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinDot.Core
import LatticeSystem.Quantum.SpinDot.Hamiltonian

/-!
# Two-site spin inner product (Tasaki §2.2 eq (2.2.16))

**Façade module** re-exporting the two-site spin inner product
machinery. Following the refactor plan v4 §3.1 (Phase 2 PR 15),
this file is a thin re-import of:

| sub-file | content |
|---|---|
| `SpinDot/Core.lean` | `spinHalfDot` def + Hermiticity + ladder decomp |
|                     | + basis-vec actions + inner-product family + SU(2) |
| `SpinDot/Hamiltonian.lean` | Heisenberg-type Hamiltonian + Casimir |
|                            | + eigenvalue propagation |
|                            | + commutativity with global rotations |
|                            | + singlet/triplet eigenvalues |

Old `import LatticeSystem.Quantum.SpinDot` continues to work
unchanged via this façade.

(Refactor Phase 2 PR 15, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

end LatticeSystem.Quantum
