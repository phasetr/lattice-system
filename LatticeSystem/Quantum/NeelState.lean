/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.NeelState.BondAction.Chain
import LatticeSystem.Quantum.NeelState.BondAction.Square
import LatticeSystem.Quantum.NeelState.BondAction.Cubic
import LatticeSystem.Quantum.NeelState.TimeReversal
import LatticeSystem.Quantum.NeelState.MarshallSign
import LatticeSystem.Quantum.NeelState.InnerProduct
import LatticeSystem.Quantum.NeelState.Energy

/-!
# Néel state — generic graph-centric + chain / 2D / 3D specialisations (Tasaki §2.5)

**Façade module** re-exporting the entire Néel state machinery.
Following the refactor plan v4 §3.1 (Phase 2 PR 1–9), this file
is now a thin re-import of nine sub-files under
`LatticeSystem/Quantum/NeelState/`:

| sub-file | content |
|---|---|
| `Definition.lean` | generic graph-centric `neelStateOf` + |
|                   | `_antiparallel` per-bond action / expectation primitives |
|                   | (Tasaki §2.5 (2.5.2)–(2.5.4) graph-centric form, Phase 3 |
|                   | PR #331 / #332); chain Néel config / state, |
|                   | magnetisation = 0, H_0 |
| `Definition2D.lean` | 2D checkerboard analogue |
| `Definition3D.lean` | 3D cubic checkerboard analogue |
| `BondAction/Chain.lean` | per-bond `Ŝ_x · Ŝ_y` action on the chain (adjacent + wrap) |
| `BondAction/Square.lean` | 2D bond action (horizontal / vertical, adjacent + wrap) |
| `BondAction/Cubic.lean` | 3D bond action (x / y / z, adjacent + wrap) |
| `TimeReversal.lean` | `Θ̂_tot · Φ_Néel` action across all dimensions |
| `MarshallSign.lean` | Marshall sign machinery (generic + chain / 2D / 3D, |
|                     | + flip + Marshall × time-reversal bridge) |
| `InnerProduct.lean` | norm² + per-bond expectation `-1/4` (S·S, S^z·S^z, parallel, off-diagonal) |
| `Energy.lean` | K=1 chain Heisenberg energy expectation `J/2` |

Old `import LatticeSystem.Quantum.NeelState` continues to work
unchanged via this façade. (Refactor Phase 2 PR 9, plan v4 §3.1.
Following the convention from `docs/refactoring-conventions.md`
§2 "Façade module policy".)
-/

namespace LatticeSystem.Quantum

end LatticeSystem.Quantum
