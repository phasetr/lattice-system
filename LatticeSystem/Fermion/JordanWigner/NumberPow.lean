import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Multi-mode Jordan–Wigner number-operator power identity
`n_i^(k+1) = n_i`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #992. For
every `k : ℕ` the per-site fermion number operator satisfies

  `n_i^(k+1) = n_i`.

Direct induction on `k` from the squared identity
`fermionMultiNumber_sq` (`Fermion/JordanWigner/Operators.lean`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `n_i^(k+1) = n_i` for every `k : ℕ` (multi-mode idempotent
projection power identity). -/
theorem fermionMultiNumber_pow_succ (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    fermionMultiNumber N i ^ (k + 1) = fermionMultiNumber N i := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionMultiNumber_sq]

end LatticeSystem.Fermion
