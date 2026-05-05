import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum

/-!
# Each all-aligned state lies in its magnetization subspace

For any constant `c : Fin (N + 1)`,

  `allAlignedStateS V N c ∈ magSubspaceS V N (|V|·N/2 − |V|·c.val)`.

Direct from `totalSpinSOp3_mulVec_allAlignedStateS` (PR earlier) +
`magEigenvalueS_allAlignedConfigS` and `mem_magSubspaceS_iff`.

For the highest weight (`c = 0`): `m_max = |V|·N/2` (matches PR #891).
For the lowest weight (`c = Fin.last N`): `−m_max = −|V|·N/2`
(matches PR #891).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `allAlignedStateS V N c ∈ magSubspaceS V N (|V|·N/2 − |V|·c.val)`. -/
theorem allAlignedStateS_mem_magSubspaceS (c : Fin (N + 1)) :
    (allAlignedStateS V N c : (V → Fin (N + 1)) → ℂ) ∈
      magSubspaceS V N
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 -
          (Fintype.card V : ℂ) * (c.val : ℂ)) := by
  rw [mem_magSubspaceS_iff]
  rw [totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS]

/-- The line spanned by `allAlignedStateS V N c` is contained in the
corresponding magnetization subspace (γ-4 step 195). -/
theorem allAlignedStateS_span_le_magSubspaceS (c : Fin (N + 1)) :
    Submodule.span ℂ {(allAlignedStateS V N c : (V → Fin (N + 1)) → ℂ)} ≤
      magSubspaceS V N
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 -
          (Fintype.card V : ℂ) * (c.val : ℂ)) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact allAlignedStateS_mem_magSubspaceS c

end LatticeSystem.Quantum
