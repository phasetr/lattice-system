import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinBridge
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorUnique
import LatticeSystem.Quantum.SpinS.TotalSquaredCore

/-!
# Fermion-Spin bridge, total-spin Casimir (Theorem 10.4 arc, PR-9b)

Eleventh installment of the Theorem 10.4 discharge arc (issue #5320); second of the two-PR 9a/9b
split of "PR-9: Fermion-Spin bridge". This file supplies the ladder-vs-Cartesian Casimir bridge
that PR-9a's module docstring flagged as separate work: `fermionTotalSpinSquared`
(`SaturatedFerromagnetism.lean`, the ladder form `Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)`) and
`totalSpinSSquared` (`Quantum/SpinS/TotalSquaredCore.lean`, the Cartesian form
`(Ŝ¹)² + (Ŝ²)² + (Ŝ³)²`) are equal as operators but not definitionally, and the fermionic
side lives on the whole Fock space while the spin-`1/2` side lives on the magnetization
sector reached via PR-9a's sector `Equiv`
(`liebHardCoreHalfFillingSectorEquivS`, `LiebRepulsiveFermionSpinBridge.lean`).

## Route

The pure SU(2)-algebra ladder-vs-Cartesian identity on the fermionic side alone is already proved:
`fermionTotalSpinSquared_eq_cartesianSqSum` (`LiebAttractiveFullSectorUnique.lean`) rewrites
`fermionTotalSpinSquared N` as `tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N *
tJTotalSpinTwo N + fermionTotalSpinZ N * fermionTotalSpinZ N`, the fermionic Cartesian components.
What remains genuinely new here is the **entrywise correspondence** of those fermionic Cartesian
(and ladder) total operators with the spin-`1/2` Cartesian totals `totalSpinSOp1`/`Op2`/`Op3`
(`Quantum/SpinS/Operators.lean`) under the hard-core half-filling sector `Equiv`, mirroring PR-9a's
`fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied` crux for the two-site dot.

## The capstone

`fermionTotalSpinSquared_apply_eq_totalSpinSSquared_of_singlyOccupied` is the crux entrywise
identity: on hard-core half-filled bra/ket Fock configurations, the fermionic Casimir's matrix
element equals the spin-`1/2` Cartesian Casimir's matrix element at the images under
`liebHardCoreDownOccupation`. It is stated directly on Fock-space matrix entries (no `submatrix`
plumbing), the same shape PR-9a's crux used.

`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector` packages the crux into the
`submatrix`-along-the-sector-`Equiv` form matching PR-9a's capstone shape, restricting
`fermionTotalSpinSquared N` to the hard-core sub-sector (via `Subtype.val`) and reindexing onto
`totalSpinSSquared (Fin (N + 1)) 1` on the magnetization-`(N + 1 − nUp)` sector.

Both proof bodies are `sorry` (TDD Red); the crux is expected to go through
`fermionTotalSpinSquared_eq_cartesianSqSum` plus an entrywise Cartesian-component correspondence
analogous to PR-9a's ladder/diagonal crux, not yet formalised here.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.10), p. 345; §2.5, Theorem 2.3, p. 42;
§11.1.1 (Casimir ladder form), p. 372.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-! ## The crux entrywise identity -/

/-- **The crux entrywise identity (PR-9b)**: on hard-core half-filled bra/ket configurations, the
fermionic total-spin Casimir's matrix element equals the spin-`1/2` Cartesian Casimir's matrix
element at the images under `liebHardCoreDownOccupation` (the down-orbital occupation read-off,
`LiebRepulsiveFermionSpinBridge.lean`).

Reference: Tasaki §11.1.1, p. 372 (ladder form); §2.5, p. 42 (Cartesian form). -/
theorem fermionTotalSpinSquared_apply_eq_totalSpinSSquared_of_singlyOccupied (N nUp : ℕ)
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionTotalSpinSquared N) e c =
      (totalSpinSSquared (Fin (N + 1)) 1) (liebHardCoreDownOccupation e)
        (liebHardCoreDownOccupation c) := by
  sorry

/-! ## The PR-9b capstone: reindexing onto the magnetization sector -/

/-- **PR-9b capstone**: `fermionTotalSpinSquared N`, restricted to the hard-core half-filling
sub-sector (`Subtype.val` inclusion into the ambient Fock space) and reindexed along PR-9a's sector
`Equiv` (`liebHardCoreHalfFillingSectorEquivS`), agrees with the spin-`1/2` Cartesian Casimir
`totalSpinSSquared (Fin (N + 1)) 1` on the magnetization-`(N + 1 − nUp)` sector.

This is the shape needed to transport the Casimir eigenvalue obtained from Theorem 2.3
(`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`,
`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean`) back to the fermionic ground states in the
later PR-11/PR-12 assembly steps of the Theorem 10.4 arc. -/
theorem fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    (fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
      = (totalSpinSSquared (Fin (N + 1)) 1).submatrix
          (fun s => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val)
          (fun s => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) := by
  sorry

end LatticeSystem.Fermion
