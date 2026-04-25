/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.String
import LatticeSystem.Fermion.JordanWigner.Operators
import LatticeSystem.Fermion.JordanWigner.CAR
import LatticeSystem.Fermion.JordanWigner.Number
import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Multi-mode fermion via Jordan–Wigner mapping

**Façade module** re-exporting the full Jordan–Wigner machinery.
Following the refactor plan v4 §3.1 (Phase 2 PR 10–14), this file
is now a thin re-import of five sub-files under
`LatticeSystem/Fermion/JordanWigner/`:

| sub-file | content |
|---|---|
| `String.lean` | JW string fundamentals |
| `Operators.lean` | multi-mode `c_i`, `c_i†`, on-site CAR, hermiticity, number op |
| `CAR.lean` | full canonical anticommutation (same-site + cross-site, factorisations) |
| `Number.lean` | number commutators, Hubbard skeleton, fermion vacuum |
| `Hubbard.lean` | spinful wrappers, on-graph Hubbard, 1D open / periodic chain Gibbs |
| `Hubbard/Charges.lean` | `N_↑`, `N_↓`, `S^z_tot`, vacuum eigenstates, cross-spin commutes |
| `Hubbard/Graph.lean` | graph-centric wrappers, chain/cycle Hamiltonians + Gibbs families |
| `Hubbard/SpinSymmetry.lean` | U(1)×U(1) charges + S^z_tot commutation with H (Tasaki §9.3.3) |

Old `import LatticeSystem.Fermion.JordanWigner` continues to
work unchanged via this façade. Following the convention from
`docs/refactoring-conventions.md` §2 "Façade module policy".

(Refactor Phase 2 PR 14, plan v4 §3.1. JordanWigner extraction
complete.)
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
