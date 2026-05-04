import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges

/-!
# Hermiticity of total spin operators

| Lean name | Statement |
|---|---|
| `fermionTotalSpinMinus_conjTranspose` | `(Ŝ^-_tot)ᴴ = Ŝ^+_tot` |
| `fermionTotalSpinZ_isHermitian` | `(Ŝ^z_tot).IsHermitian` |
| `fermionTotalSpinSquared_isHermitian` | `(Ŝ²_tot).IsHermitian` |

`(Ŝ^-)ᴴ = Ŝ^+` follows from
`fermionTotalSpinPlus_conjTranspose` by taking `conjTranspose`
of both sides.

`Ŝ^z = (1/2)(N_↑ − N_↓)` is Hermitian since the difference of
the Hermitian `N_↑, N_↓` is Hermitian and the scalar `1/2` is
real.

`Ŝ²_tot = Ŝ^- Ŝ^+ + Ŝ^z (Ŝ^z + 1)` is Hermitian:
- `(Ŝ^- Ŝ^+)ᴴ = (Ŝ^+)ᴴ (Ŝ^-)ᴴ = Ŝ^- Ŝ^+`,
- `Ŝ^z (Ŝ^z + 1)` is a polynomial in the Hermitian `Ŝ^z`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `(Ŝ^-_tot)ᴴ = Ŝ^+_tot` (dual of
`fermionTotalSpinPlus_conjTranspose`). -/
theorem fermionTotalSpinMinus_conjTranspose (N : ℕ) :
    (fermionTotalSpinMinus N)ᴴ = fermionTotalSpinPlus N := by
  have h := fermionTotalSpinPlus_conjTranspose N
  -- h : (S^+)ᴴ = S^-.
  -- So ((S^+)ᴴ)ᴴ = (S^-)ᴴ, i.e. S^+ = (S^-)ᴴ.
  have h2 := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_conjTranspose] at h2
  exact h2.symm

/-- `Ŝ^z_tot = (1/2)(N_↑ − N_↓)` is Hermitian. -/
theorem fermionTotalSpinZ_isHermitian (N : ℕ) :
    (fermionTotalSpinZ N).IsHermitian := by
  unfold Matrix.IsHermitian fermionTotalSpinZ
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    (fermionTotalUpNumber_isHermitian N).eq,
    (fermionTotalDownNumber_isHermitian N).eq,
    show star ((1 : ℂ) / 2) = (1 : ℂ) / 2 from by simp]

/-- `Ŝ²_tot = Ŝ^- Ŝ^+ + Ŝ^z (Ŝ^z + 1)` is Hermitian. -/
theorem fermionTotalSpinSquared_isHermitian (N : ℕ) :
    (fermionTotalSpinSquared N).IsHermitian := by
  unfold Matrix.IsHermitian fermionTotalSpinSquared
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionTotalSpinPlus_conjTranspose N,
    fermionTotalSpinMinus_conjTranspose N,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one,
    (fermionTotalSpinZ_isHermitian N).eq]
  -- Goal: ... + (S_z + 1) * S_z = ... + S_z * (S_z + 1).
  -- Use that 1 commutes with S_z.
  congr 1
  rw [mul_add, add_mul, Matrix.one_mul, Matrix.mul_one]

end LatticeSystem.Fermion
