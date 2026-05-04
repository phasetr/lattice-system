import LatticeSystem.Fermion.JordanWigner.String
import LatticeSystem.Fermion.JordanWigner.Operators
import LatticeSystem.Fermion.JordanWigner.CAR
import LatticeSystem.Fermion.JordanWigner.Number
import LatticeSystem.Fermion.JordanWigner.NumberAnticommutators
import LatticeSystem.Fermion.JordanWigner.NumberPow
import LatticeSystem.Fermion.JordanWigner.CDaggerCCommutator
import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity
import LatticeSystem.Fermion.JordanWigner.CDaggerCProjection
import LatticeSystem.Fermion.JordanWigner.CDaggerCHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism

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
| `NumberAnticommutators.lean` | same-site `{n_i, c_i}`, `{n_i, c_i†}` anticommutators |
| `NumberPow.lean` | `n_i^(k+1) = n_i` (idempotent projection power) |
| `CDaggerCCommutator.lean` | same-site `[c_i, c_i†] = 1 − 2·n_i` |
| `CDaggerCIdentity.lean` | same-site `c_i · c_i† = 1 − n_i`, `n_i + c_i · c_i† = 1` |
| `CDaggerCProjection.lean` | hole-projection idempotency `(c_i · c_i†)² = c_i · c_i†` + powers |
| `CDaggerCHermitian.lean` | hole projection Hermitian `(c_i · c_i†)ᴴ = c_i · c_i†` |
| `Hubbard.lean` | spinful wrappers, on-graph Hubbard, 1D open / periodic chain Gibbs |
| `Hubbard/Charges.lean` | `N_↑`, `N_↓`, `S^z_tot`, vacuum eigenstates, cross-spin commutes |
| `Hubbard/Graph.lean` | graph-centric wrappers, chain/cycle Hamiltonians + Gibbs families |
| `Hubbard/SpinSymmetry.lean` | U(1)×U(1) charges + S^z_tot commutation with H (Tasaki §9.3.3) |
| `Hubbard/AllUpState.lean` | all-up state: H_kin eigenvalue, no double occupancy |
| `Hubbard/SaturatedFerromagnetism.lean` | spin Casimir, Def 11.1, SU(2) algebra |

Old `import LatticeSystem.Fermion.JordanWigner` continues to
work unchanged via this façade. Following the convention from
`docs/refactoring-conventions.md` §2 "Façade module policy".

(Refactor Phase 2 PR 14, plan v4 §3.1. JordanWigner extraction
complete.)
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
