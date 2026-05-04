import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulNumberHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Hubbard per-site projections p_∅, p_↑, p_↓ are Hermitian

Companion Hermiticity lemmas to PR #1007 (`p_⇈.IsHermitian`):

  `((1 − n_↑(i)) · (1 − n_↓(i))).IsHermitian`,  (`p_∅`)
  `(n_↑(i) · (1 − n_↓(i))).IsHermitian`,         (`p_↑`)
  `((1 − n_↑(i)) · n_↓(i)).IsHermitian`.          (`p_↓`)

Each is a product of two commuting Hermitian factors:
- `(1 − n_σ).IsHermitian` via `Matrix.IsHermitian.sub` with
  `Matrix.isHermitian_one`,
- `Commute (1 − n_σ) m_τ` propagated from
  `Commute n_↑ n_↓` (PR #1005) by ring algebra,
- `Matrix.IsHermitian.mul_of_commute`.

Together with PR #1007 these establish that all four per-site
occupation projections (PR #1011) are Hermitian projections.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma one_sub_fermionUpNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionUpNumber N i).IsHermitian :=
  (Matrix.isHermitian_one (n := Fin (2 * N + 2) → Fin 2) (α := ℂ)).sub
    (fermionUpNumber_isHermitian N i)

private lemma one_sub_fermionDownNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionDownNumber N i).IsHermitian :=
  (Matrix.isHermitian_one (n := Fin (2 * N + 2) → Fin 2) (α := ℂ)).sub
    (fermionDownNumber_isHermitian N i)

private lemma one_sub_fermionUpNumber_commute_one_sub_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (1 - fermionUpNumber N i) (1 - fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionUpNumber_commute_fermionDownNumber N i).eq
  rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionUpNumber N i) *
      (1 - fermionDownNumber N i) =
      1 - fermionDownNumber N i - fermionUpNumber N i +
        fermionUpNumber N i * fermionDownNumber N i from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel,
    show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionDownNumber N i) *
      (1 - fermionUpNumber N i) =
      1 - fermionUpNumber N i - fermionDownNumber N i +
        fermionDownNumber N i * fermionUpNumber N i from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [hcomm]
  abel

private lemma fermionUpNumber_commute_one_sub_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpNumber N i) (1 - fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionUpNumber_commute_fermionDownNumber N i).eq
  rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm]

private lemma one_sub_fermionUpNumber_commute_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (1 - fermionUpNumber N i) (fermionDownNumber N i) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionUpNumber_commute_fermionDownNumber N i).eq
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

/-- `((1 − n_↑(i)) · (1 − n_↓(i))).IsHermitian` (Hubbard empty
per-site projection is Hermitian). -/
theorem one_sub_fermionUpNumber_mul_one_sub_fermionDownNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute
    (one_sub_fermionUpNumber_isHermitian N i)
    (one_sub_fermionDownNumber_isHermitian N i)
    (one_sub_fermionUpNumber_commute_one_sub_fermionDownNumber N i)

/-- `(n_↑(i) · (1 − n_↓(i))).IsHermitian` (Hubbard only-up
per-site projection is Hermitian). -/
theorem fermionUpNumber_mul_one_sub_fermionDownNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute
    (fermionUpNumber_isHermitian N i)
    (one_sub_fermionDownNumber_isHermitian N i)
    (fermionUpNumber_commute_one_sub_fermionDownNumber N i)

/-- `((1 − n_↑(i)) · n_↓(i)).IsHermitian` (Hubbard only-down
per-site projection is Hermitian). -/
theorem one_sub_fermionUpNumber_mul_fermionDownNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute
    (one_sub_fermionUpNumber_isHermitian N i)
    (fermionDownNumber_isHermitian N i)
    (one_sub_fermionUpNumber_commute_fermionDownNumber N i)

end LatticeSystem.Fermion
