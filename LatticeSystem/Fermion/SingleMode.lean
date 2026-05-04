import LatticeSystem.Fermion.Mode
import LatticeSystem.Fermion.AnnihilationCreationIdentity
import LatticeSystem.Fermion.AnnihilationNumberIdentities
import LatticeSystem.Fermion.CCDaggerAction
import LatticeSystem.Fermion.CCDaggerCommutator
import LatticeSystem.Fermion.CCDaggerExpectations
import LatticeSystem.Fermion.CCDaggerHermitian
import LatticeSystem.Fermion.CCDaggerIdempotent
import LatticeSystem.Fermion.CCDaggerLadderZero
import LatticeSystem.Fermion.CCDaggerSpinSBridge
import LatticeSystem.Fermion.CPlusCDaggerSq
import LatticeSystem.Fermion.CreationNumberIdentities
import LatticeSystem.Fermion.NumberExpectations
import LatticeSystem.Fermion.NumberLadderAnticommutators
import LatticeSystem.Fermion.NumberLadderCommutators
import LatticeSystem.Fermion.NumberSpinSBridge
import LatticeSystem.Fermion.PartialIsometry
import LatticeSystem.Fermion.ProjectionPow
import LatticeSystem.Fermion.ProjectionsCommute
import LatticeSystem.Fermion.ProjectionsOrthogonal
import LatticeSystem.Fermion.ProjectionSum
import LatticeSystem.Fermion.SpinSBridge
import LatticeSystem.Fermion.StatesOrthonormal
import LatticeSystem.Fermion.Traces

/-!
# Single-mode fermion algebra (façade)

**Façade module** re-exporting the full single-mode fermion
algebra developed during the 2026-05-04 autonomous fermion
expansion (PRs #988–#1021), on top of the original `Mode.lean`
core.

| sub-file | content |
|---|---|
| `Mode.lean` | core defs + CAR + Hermiticity + basis actions |
| `AnnihilationCreationIdentity.lean` | `c · c† = 1 − n` |
| `AnnihilationNumberIdentities.lean` | `n · c = 0`, `c · n = c` |
| `CCDaggerAction.lean` | `(c · c†) · |0⟩ = |0⟩`, `(c · c†) · |1⟩ = 0` |
| `CCDaggerCommutator.lean` | `[c, c†] = 1 − 2 · n` |
| `CCDaggerExpectations.lean` | `⟨c · c†⟩` on basis states |
| `CCDaggerHermitian.lean` | `(c · c†)ᴴ = c · c†` |
| `CCDaggerIdempotent.lean` | `(c · c†)² = c · c†` |
| `CCDaggerLadderZero.lean` | `c · (c · c†) = 0`, `(c · c†) · c† = 0` |
| `CCDaggerSpinSBridge.lean` | `c · c† = (1/2) · I + spinSOp3 1` |
| `CPlusCDaggerSq.lean` | `(c + c†)² = 1` (X-Pauli analog) |
| `CreationNumberIdentities.lean` | `c† · n = 0`, `n · c† = c†` |
| `NumberExpectations.lean` | `⟨n⟩` on basis states |
| `NumberLadderAnticommutators.lean` | `{n, c} = c`, `{n, c†} = c†` |
| `NumberLadderCommutators.lean` | `[n, c] = -c`, `[n, c†] = c†` |
| `NumberSpinSBridge.lean` | `n = (1/2) · I − spinSOp3 1` |
| `PartialIsometry.lean` | `c · c† · c = c`, `c† · c · c† = c†` |
| `ProjectionPow.lean` | `n^(k+1) = n`, `(c · c†)^(k+1) = c · c†` |
| `ProjectionsCommute.lean` | `Commute n (c · c†)` |
| `ProjectionsOrthogonal.lean` | `n · (c · c†) = 0`, `(c · c†) · n = 0` |
| `ProjectionSum.lean` | `n + c · c† = 1` |
| `SpinSBridge.lean` | `c = spinSOpPlus 1`, `c† = spinSOpMinus 1` |
| `StatesOrthonormal.lean` | vacuum/occupied orthonormality |
| `Traces.lean` | `tr(c) = tr(c†) = 0`, `tr(n) = tr(c · c†) = 1` |

Old `import LatticeSystem.Fermion.Mode` continues to work
unchanged via this façade. A downstream `import LatticeSystem.Fermion.SingleMode`
exposes the full single-mode algebra.
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
