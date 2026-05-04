import LatticeSystem.Fermion.Mode

/-!
# Single-mode fermion `(1 − 2 · n)² = 1` (σ_z analog involution)

For the single-mode fermion the Pauli-σ_z analog is involutive:

  `(1 − 2 · n)² = 1`.

Direct from `n² = n` (`fermionNumber_sq`):

  `(1 − 2n)² = 1 − 4n + 4n² = 1 − 4n + 4n = 1`.

Physics identification: `1 − 2n = σ_z` (in our convention
`n = (I − σ_z)/2`), and `σ_z² = I`. Together with
- `(c + c†)² = 1` (PR #1021), and
- `(c − c†)² = −1` (PR #1023)
this completes the single-mode Pauli-analog `σ_α² = ±1`
involution identities.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(1 − 2 · n)² = 1` (single-mode `σ_z` analog involution). -/
theorem one_sub_two_smul_fermionNumber_sq :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (2 : ℂ) • fermionNumber) *
        (1 - (2 : ℂ) • fermionNumber) =
      1 := by
  -- Replace `2 • n` with `n + n`.
  rw [show (2 : ℂ) • fermionNumber = fermionNumber + fermionNumber from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  -- (1 - n - n) * (1 - n - n) expanded.
  rw [show (1 - (fermionNumber + fermionNumber)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) - fermionNumber - fermionNumber from by abel]
  rw [show ((1 : Matrix (Fin 2) (Fin 2) ℂ) - fermionNumber - fermionNumber) *
        (1 - fermionNumber - fermionNumber) =
      1 - fermionNumber - fermionNumber - fermionNumber - fermionNumber +
        (fermionNumber * fermionNumber + fermionNumber * fermionNumber +
          (fermionNumber * fermionNumber + fermionNumber * fermionNumber)) from by
    rw [sub_mul, sub_mul, mul_sub, mul_sub, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [fermionNumber_sq]
  abel

end LatticeSystem.Fermion
