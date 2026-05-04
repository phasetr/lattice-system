import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsIdempotent

/-!
# Hubbard per-site projection power identities

For every `k : ℕ` each of the four per-site Hubbard occupation
projections satisfies the positive-degree power identity:

  `(p_⇈(i))^(k+1) = p_⇈(i)`,
  `(p_∅(i))^(k+1) = p_∅(i)`,
  `(p_↑(i))^(k+1) = p_↑(i)`,
  `(p_↓(i))^(k+1) = p_↓(i)`.

Each by direct induction on `k` from the squared identities in
PRs #1005 (`p_⇈²= p_⇈`) and #1012 (the other three squared
identities). Mirrors PR #992 (single-mode `n^(k+1) = n` and
`(c·c†)^(k+1) = c·c†`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(p_⇈(i))^(k+1) = p_⇈(i)`. -/
theorem fermionDoublyProjection_pow_succ
    (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    (fermionUpNumber N i * fermionDownNumber N i) ^ (k + 1) =
      fermionUpNumber N i * fermionDownNumber N i := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionUpNumber_mul_fermionDownNumber_sq]

/-- `(p_∅(i))^(k+1) = p_∅(i)`. -/
theorem fermionEmptyProjection_pow_succ
    (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) ^ (k + 1) =
      (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, one_sub_fermionUpNumber_mul_one_sub_fermionDownNumber_sq]

/-- `(p_↑(i))^(k+1) = p_↑(i)`. -/
theorem fermionUpProjection_pow_succ
    (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)) ^ (k + 1) =
      fermionUpNumber N i * (1 - fermionDownNumber N i) := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionUpNumber_mul_one_sub_fermionDownNumber_sq]

/-- `(p_↓(i))^(k+1) = p_↓(i)`. -/
theorem fermionDownProjection_pow_succ
    (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i) ^ (k + 1) =
      (1 - fermionUpNumber N i) * fermionDownNumber N i := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, one_sub_fermionUpNumber_mul_fermionDownNumber_sq]

end LatticeSystem.Fermion
