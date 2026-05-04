import LatticeSystem.Fermion.JordanWigner.CAR.SameSite
import LatticeSystem.Fermion.JordanWigner.CAR.StringFactorization
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSite
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Jordan–Wigner canonical anticommutation relations — façade

**Façade module** re-exporting the full CAR algebra split into
sub-files (codex audit Item 10, tracked in #390; extended with
`CrossSiteOfNe` during the 2026-05-04 fermion-algebra expansion):

| sub-file | content |
|---|---|
| `CAR/SameSite.lean` | number operators, same-site CAR, |
|                     | small-N explicit cross-site cases |
| `CAR/StringFactorization.lean` | JW string factorisation, interior anticommutators, |
|                                | string commutativity, zero-site general CAR |
| `CAR/CrossSite.lean` | fully general `{c_i, c_j} = 0` for arbitrary `i < j` |
| `CAR/CrossSiteOfNe.lean` | symmetric `_of_ne` versions of all 4 cross-site CAR |

Existing code that imports `LatticeSystem.Fermion.JordanWigner.CAR`
continues to work unchanged via this façade.

(Refactor Phase 2 PR 12 — third step of the JordanWigner 5-file
split, plan v4 §3.1. Codex audit Item 10: sub-split into 3 files.
2026-05-04: extended with `CrossSiteOfNe`.)
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
