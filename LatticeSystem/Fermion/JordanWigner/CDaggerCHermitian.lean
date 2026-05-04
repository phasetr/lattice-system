import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Multi-mode Jordan–Wigner hole projection is Hermitian

Multi-mode (Jordan–Wigner) mirror of single-mode PR #980. The
hole-occupation operator at site `i` is Hermitian:

  `(c_i · c_i†)ᴴ = c_i · c_i†`.

Direct from
- `(c_i)ᴴ = c_i†` (`fermionMultiAnnihilation_conjTranspose`) and
- `(c_i†)ᴴ = c_i` (`fermionMultiCreation_conjTranspose`),

via `(c_i · c_i†)ᴴ = (c_i†)ᴴ · (c_i)ᴴ = c_i · c_i†`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `(c_i · c_i†)ᴴ = c_i · c_i†` (multi-mode hole projection is
Hermitian). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i * fermionMultiCreation N i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose]

end LatticeSystem.Fermion
