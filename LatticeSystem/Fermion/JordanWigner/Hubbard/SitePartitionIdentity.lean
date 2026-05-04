import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Hubbard per-site 4-state partition of identity

For each spinful Hubbard site `i` the four occupation
projections

  `p_∅(i)  := (1 − n_↑(i)) · (1 − n_↓(i))`  (empty)
  `p_↑(i)  := n_↑(i) · (1 − n_↓(i))`         (only up)
  `p_↓(i)  := (1 − n_↑(i)) · n_↓(i)`         (only down)
  `p_⇈(i)  := n_↑(i) · n_↓(i)`               (doubly occupied)

partition the identity:

  `p_∅(i) + p_↑(i) + p_↓(i) + p_⇈(i) = 1`.

Direct algebraic identity from distributing
`((1 − n_↑) + n_↑) · ((1 − n_↓) + n_↓) = 1 · 1 = 1`
which uses only `(1 − n_σ) + n_σ = 1`.

This is the standard 4-state per-site decomposition underlying
the Hubbard Hilbert-space tensor structure
`ℂ⁴ = |0,0⟩ ⊕ |1,0⟩ ⊕ |0,1⟩ ⊕ |1,1⟩`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- The four spinful per-site occupation projections sum to the
identity:
`(1 − n_↑) (1 − n_↓) + n_↑ (1 − n_↓) + (1 − n_↑) n_↓ + n_↑ n_↓
 = 1`. -/
theorem fermionUpDownNumber_site_partition_eq_one
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
        fermionUpNumber N i * (1 - fermionDownNumber N i) +
      ((1 - fermionUpNumber N i) * fermionDownNumber N i +
        fermionUpNumber N i * fermionDownNumber N i) =
      (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  -- Group by left factor: ((1 - n_↑) + n_↑) * (1 - n_↓) +
  --                         ((1 - n_↑) + n_↑) * n_↓
  --                       = 1 * (1 - n_↓) + 1 * n_↓
  --                       = (1 - n_↓) + n_↓ = 1.
  rw [show (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
          fermionUpNumber N i * (1 - fermionDownNumber N i) =
        ((1 - fermionUpNumber N i) + fermionUpNumber N i) *
          (1 - fermionDownNumber N i) from by rw [add_mul],
      show (1 - fermionUpNumber N i) * fermionDownNumber N i +
          fermionUpNumber N i * fermionDownNumber N i =
        ((1 - fermionUpNumber N i) + fermionUpNumber N i) *
          fermionDownNumber N i from by rw [add_mul]]
  rw [show (1 - fermionUpNumber N i) + fermionUpNumber N i =
      (1 : ManyBodyOp (Fin (2 * N + 2))) from by abel]
  rw [Matrix.one_mul, Matrix.one_mul]
  abel

end LatticeSystem.Fermion
