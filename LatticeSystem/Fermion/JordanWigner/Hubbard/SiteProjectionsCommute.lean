import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsUpDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsEmptySingle
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsSingleDoubly

/-!
# Hubbard same-site per-site projections pairwise commute

The four per-site Hubbard occupation projections at the same
site `i` pairwise commute:

  `Commute (p_α(i)) (p_β(i))` for any `α, β ∈ {∅, ↑, ↓, ⇈}`.

For `α ≠ β` these are trivial corollaries of the
cross-orthogonality results (PRs #1014, #1016, #1017, #1018):
both `p_α · p_β = 0` and `p_β · p_α = 0`, so the products are
equal.

Together with PRs #1005 and #1006 (cross-site `Commute n_↑ n_↓`
and `Commute (n_↑·n_↓)(i) (n_↑·n_↓)(j)`), the per-site
projection algebra is fully commutative on top of being a
complete orthogonal partition (PRs #1011, #1014, #1016--#1018).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute p_⇈(i) p_∅(i)`: doubly-occupied and empty per-site
projections commute (both products vanish). -/
theorem fermionDoublyProjection_commute_fermionEmptyProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpNumber N i * fermionDownNumber N i)
      ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) := by
  unfold Commute SemiconjBy
  rw [fermionUpDownNumber_mul_empty_eq_zero,
    empty_mul_fermionUpDownNumber_eq_zero]

/-- `Commute p_↑(i) p_↓(i)`: only-up and only-down per-site
projections commute (both products vanish). -/
theorem fermionUpProjection_commute_fermionDownProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpNumber N i * (1 - fermionDownNumber N i))
      ((1 - fermionUpNumber N i) * fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  rw [fermionUpProjection_mul_fermionDownProjection_eq_zero,
    fermionDownProjection_mul_fermionUpProjection_eq_zero]

/-- `Commute p_∅(i) p_↑(i)`. -/
theorem fermionEmptyProjection_commute_fermionUpProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i))
      (fermionUpNumber N i * (1 - fermionDownNumber N i)) := by
  unfold Commute SemiconjBy
  rw [fermionEmptyProjection_mul_fermionUpProjection_eq_zero,
    fermionUpProjection_mul_fermionEmptyProjection_eq_zero]

/-- `Commute p_∅(i) p_↓(i)`. -/
theorem fermionEmptyProjection_commute_fermionDownProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i))
      ((1 - fermionUpNumber N i) * fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  rw [fermionEmptyProjection_mul_fermionDownProjection_eq_zero,
    fermionDownProjection_mul_fermionEmptyProjection_eq_zero]

/-- `Commute p_↑(i) p_⇈(i)`. -/
theorem fermionUpProjection_commute_fermionDoublyProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpNumber N i * (1 - fermionDownNumber N i))
      (fermionUpNumber N i * fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  rw [fermionUpProjection_mul_fermionDoublyProjection_eq_zero,
    fermionDoublyProjection_mul_fermionUpProjection_eq_zero]

/-- `Commute p_↓(i) p_⇈(i)`. -/
theorem fermionDownProjection_commute_fermionDoublyProjection
    (N : ℕ) (i : Fin (N + 1)) :
    Commute ((1 - fermionUpNumber N i) * fermionDownNumber N i)
      (fermionUpNumber N i * fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  rw [fermionDownProjection_mul_fermionDoublyProjection_eq_zero,
    fermionDoublyProjection_mul_fermionDownProjection_eq_zero]

end LatticeSystem.Fermion
