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
import LatticeSystem.Fermion.JordanWigner.ProjectionsOrthogonal
import LatticeSystem.Fermion.JordanWigner.ProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.AnnihilationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.CreationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.PartialIsometry
import LatticeSystem.Fermion.JordanWigner.HoleProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.HoleProjectionCommuteLadder
import LatticeSystem.Fermion.JordanWigner.HoleProjectionCommuteNumber
import LatticeSystem.Fermion.JordanWigner.CDaggerCLadderZero
import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulNumberHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SitePartitionIdentity
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsIdempotent
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsUpDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsEmptySingle
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsSingleDoubly
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsSpinResolved

/-!
# Multi-mode fermion via Jordan–Wigner mapping

**Façade module** re-exporting the full Jordan–Wigner machinery.
Following the refactor plan v4 §3.1 (Phase 2 PR 10–14), this file
is a thin re-import of the sub-files under
`LatticeSystem/Fermion/JordanWigner/` (originally five core
files; further extended with single-mode-mirror and Hubbard
algebra lemmas during the 2026-05-04 autonomous fermion
expansion):

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
| `ProjectionsOrthogonal.lean` | `n_i · (c_i · c_i†) = 0`, `(c_i · c_i†) · n_i = 0` |
| `ProjectionsCommute.lean` | `Commute n_i (c_i · c_i†)` (both products zero) |
| `AnnihilationNumberIdentities.lean` | `n_i · c_i = 0`, `c_i · n_i = c_i` |
| `CreationNumberIdentities.lean` | `c_i† · n_i = 0`, `n_i · c_i† = c_i†` |
| `PartialIsometry.lean` | `c_i · c_i† · c_i = c_i`, `c_i† · c_i · c_i† = c_i†` |
| `HoleProjectionsCommute.lean` | `Commute (c_i · c_i†) (c_j · c_j†)` for any `i, j` |
| `HoleProjectionCommuteLadder.lean` | `Commute (c_i · c_i†) c_j` and `…c_j†` for `i ≠ j` |
| `HoleProjectionCommuteNumber.lean` | `Commute (c_i · c_i†) n_j` for any `i, j` |
| `CDaggerCLadderZero.lean` | `c_i · (c_i · c_i†) = 0`, `(c_i · c_i†) · c_i† = 0` |
| `Hubbard.lean` | spinful wrappers, on-graph Hubbard, 1D open / periodic chain Gibbs |
| `Hubbard/Charges.lean` | `N_↑`, `N_↓`, `S^z_tot`, vacuum eigenstates, cross-spin commutes |
| `Hubbard/Graph.lean` | graph-centric wrappers, chain/cycle Hamiltonians + Gibbs families |
| `Hubbard/SpinSymmetry.lean` | U(1)×U(1) charges + S^z_tot commutation with H (Tasaki §9.3.3) |
| `Hubbard/AllUpState.lean` | all-up state: H_kin eigenvalue, no double occupancy |
| `Hubbard/SaturatedFerromagnetism.lean` | spin Casimir, Def 11.1, SU(2) algebra |
| `Hubbard/DoubleOccupancyProjection.lean` | site-`i` `Commute n_↑ n_↓` + idempotent product |
| `Hubbard/DoubleOccupancyCommute.lean` | cross-site `Commute (n_↑(i)·n_↓(i)) (n_↑(j)·n_↓(j))` |
| `Hubbard/SpinfulNumberHermitian.lean` | `n_↑(i)`, `n_↓(i)`, `n_↑(i)·n_↓(i)` Hermitian |
| `Hubbard/SitePartitionIdentity.lean` | per-site `p_∅+p_↑+p_↓+p_⇈ = 1` (4-state partition) |
| `Hubbard/SiteProjectionsIdempotent.lean` | `(p_∅)² = p_∅`, `(p_↑)² = p_↑`, `(p_↓)² = p_↓` |
| `Hubbard/SiteProjectionsDoublyEmpty.lean` | `p_⇈ · p_∅ = 0`, `p_∅ · p_⇈ = 0` |
| `Hubbard/SiteProjectionsHermitian.lean` | `p_∅`, `p_↑`, `p_↓` Hermitian (companions to PR #1007) |
| `Hubbard/SiteProjectionsUpDown.lean` | `p_↑ · p_↓ = 0`, `p_↓ · p_↑ = 0` |
| `Hubbard/SiteProjectionsEmptySingle.lean` | `p_∅ ⊥ p_↑`, `p_∅ ⊥ p_↓` (both orderings) |
| `Hubbard/SiteProjectionsSingleDoubly.lean` | `p_↑ ⊥ p_⇈`, `p_↓ ⊥ p_⇈` (completes 6/6 ortho.) |
| `Hubbard/SiteProjectionsSpinResolved.lean` | `p_↑+p_⇈ = n_↑`, `p_∅+p_↑ = 1−n_↓`, etc. |

Old `import LatticeSystem.Fermion.JordanWigner` continues to
work unchanged via this façade. Following the convention from
`docs/refactoring-conventions.md` §2 "Façade module policy".

(Refactor Phase 2 PR 14, plan v4 §3.1. JordanWigner extraction
complete.)
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
