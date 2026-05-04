import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity
import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner hole projections commute
`Commute (c_i · c_i†) (c_j · c_j†)`

For any two sites `i, j` the hole projections at those sites
commute:

  `Commute (c_i · c_i†) (c_j · c_j†)`.

Direct from
- `c_i · c_i† = 1 − n_i` (PR #996), and
- `Commute n_i n_j` (`fermionMultiNumber_commute`,
  `Fermion/JordanWigner/CAR/SameSite.lean`)

via `Commute (1 − n_i) (1 − n_j)`, which follows from
`Commute n_i n_j` by the standard Commute calculus on
`1` and subtraction.

This complements PR #1000 (`Commute n_i (c_i · c_i†)`) by
showing all pairs of hole projections commute, regardless of
site.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute (c_i · c_i†) (c_j · c_j†)`: multi-mode hole
projections at any two sites commute. -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_commute
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute
      (fermionMultiAnnihilation N i * fermionMultiCreation N i)
      (fermionMultiAnnihilation N j * fermionMultiCreation N j) := by
  -- Reduce to (1 - n_i) and (1 - n_j); use Commute n_i n_j.
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number,
    fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  -- Both `1 - n_i` and `1 - n_j` are polynomials in commuting `n_i, n_j`.
  have hcomm : fermionMultiNumber N i * fermionMultiNumber N j =
      fermionMultiNumber N j * fermionMultiNumber N i :=
    (fermionMultiNumber_commute N i j).eq
  unfold Commute SemiconjBy
  -- LHS: (1 - n_i) * (1 - n_j) = 1 - n_j - n_i + n_i * n_j
  -- RHS: (1 - n_j) * (1 - n_i) = 1 - n_i - n_j + n_j * n_i
  -- Equal by hcomm.
  rw [show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i) *
        ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N j) =
      1 - fermionMultiNumber N j - fermionMultiNumber N i +
        fermionMultiNumber N i * fermionMultiNumber N j from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel,
    show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N j) *
        ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i) =
      1 - fermionMultiNumber N i - fermionMultiNumber N j +
        fermionMultiNumber N j * fermionMultiNumber N i from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [hcomm]
  abel

end LatticeSystem.Fermion
