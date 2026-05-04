import LatticeSystem.Fermion.JordanWigner.Number

/-!
# Multi-mode Jordan–Wigner ladder anticommutators
`{n_i, c_i} = c_i` and `{n_i, c_i†} = c_i†`

Multi-mode (per-site) version of the single-mode anticommutators
of PR #990. The two same-site anticommutator identities

  `{n_i, c_i}  = n_i · c_i  + c_i  · n_i = c_i`,
  `{n_i, c_i†} = n_i · c_i† + c_i† · n_i = c_i†`

reduce to `0 + c_i = c_i` (resp.\ `c_i† + 0 = c_i†`) via the same
per-product computations used inside the existing commutator
proofs in `Fermion/JordanWigner/Number.lean`:

- `n_i · c_i  = 0`  (from `σ⁺_i · σ⁺_i = 0`).
- `c_i · n_i  = c_i`  (from `σ⁺_i · σ⁻_i · σ⁺_i = σ⁺_i`).
- The dual pair via `Matrix.conjTranspose`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- Multi-mode anticommutator: `{n_i, c_i} = c_i`. -/
theorem fermionMultiNumber_anticommutator_fermionMultiAnnihilation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiAnnihilation N i +
        fermionMultiAnnihilation N i * fermionMultiNumber N i =
      fermionMultiAnnihilation N i := by
  rw [fermionMultiNumber_eq_onSite]
  unfold fermionMultiAnnihilation
  -- n_i · c_i = onSite i (σ^- σ^+) · jwString N i · onSite i σ^+
  --         = jwString N i · onSite i (σ^- σ^+ · σ^+) = 0.
  have hcomm_jw_minusPlus : Commute (jwString N i)
      (onSite i (spinHalfOpMinus * spinHalfOpPlus)) :=
    jwString_commute_onSite N i (spinHalfOpMinus * spinHalfOpPlus)
  have hncv : onSite i (spinHalfOpMinus * spinHalfOpPlus) *
      (jwString N i * onSite i spinHalfOpPlus) = 0 := by
    rw [← Matrix.mul_assoc, ← hcomm_jw_minusPlus.eq, Matrix.mul_assoc,
      onSite_mul_onSite_same]
    rw [show spinHalfOpMinus * spinHalfOpPlus * spinHalfOpPlus = 0 from by
      rw [Matrix.mul_assoc, spinHalfOpPlus_mul_self, Matrix.mul_zero]]
    rw [show onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ) =
        (0 : ManyBodyOp (Fin (N + 1))) from by ext σ' σ; simp [onSite_apply]]
    rw [Matrix.mul_zero]
  -- c_i · n_i = jwString N i · onSite i (σ^+ · σ^- σ^+) = jwString N i · onSite i σ^+ = c_i.
  have hcvn : (jwString N i * onSite i spinHalfOpPlus) *
      onSite i (spinHalfOpMinus * spinHalfOpPlus) =
      jwString N i * onSite i spinHalfOpPlus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_same]
    rw [show spinHalfOpPlus * (spinHalfOpMinus * spinHalfOpPlus) = spinHalfOpPlus from
      by rw [← Matrix.mul_assoc, spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus]]
  rw [hncv, hcvn, zero_add]

/-- Dual: `{n_i, c_i†} = c_i†`. Direct consequence of
`fermionMultiNumber_anticommutator_fermionMultiAnnihilation_self`
by taking `conjTranspose`. -/
theorem fermionMultiNumber_anticommutator_fermionMultiCreation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiCreation N i +
        fermionMultiCreation N i * fermionMultiNumber N i =
      fermionMultiCreation N i := by
  have h := fermionMultiNumber_anticommutator_fermionMultiAnnihilation_self N i
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    (fermionMultiNumber_isHermitian N i).eq] at h2
  -- h2 : c_i† · n_i + n_i · c_i† = c_i†
  simpa [add_comm] using h2

end LatticeSystem.Fermion
