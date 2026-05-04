import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner `(c_i + c_i†)² = 1`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #1021:
the symmetric Hermitian per-site combination is an involution

  `(c_i + c_i†)² = 1`.

Direct expansion `(c_i + c_i†)² = c_i² + c_i·c_i† + c_i†·c_i +
(c_i†)² = 0 + 1 + 0 = 1` via
- `c_i² = 0` (`fermionMultiAnnihilation_sq`),
- `(c_i†)² = 0` (`fermionMultiCreation_sq`),
- `c_i · c_i† + c_i† · c_i = 1` (`fermionMultiAnticomm_self`).

Multi-mode `σ_x`-analog: in the JW representation
`c_i + c_i† = jwString_i · (σ⁺_i + σ⁻_i) = jwString_i · σ_x_i`,
and `(jwString_i · σ_x_i)² = jwString_i² · σ_x_i² = 1 · 1 = 1`
since `jwString_i` is involutive (`jwString_sq`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(c_i + c_i†)² = 1`: multi-mode JW Hermitian symmetric
combination is an involution. -/
theorem fermionMultiAnnihilation_add_fermionMultiCreation_sq
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i + fermionMultiCreation N i) =
      (1 : ManyBodyOp (Fin (N + 1))) := by
  -- Expand: (c_i + c_i†)² = c_i² + c_i·c_i† + c_i†·c_i + (c_i†)².
  rw [add_mul, mul_add, mul_add, fermionMultiAnnihilation_sq,
    fermionMultiCreation_sq, zero_add, add_zero]
  -- Goal: c_i · c_i† + c_i† · c_i = 1.
  exact fermionMultiAnticomm_self N i

end LatticeSystem.Fermion
