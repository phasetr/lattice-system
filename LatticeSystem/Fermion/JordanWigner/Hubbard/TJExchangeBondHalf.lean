import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondPSD
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki 11.5.3: the Heisenberg bond is `½ Δ_xy† Δ_xy`, hence PSD (Theorem 11.26 PR3d)

From the CAR identity (`tJSingletAnnihilation_conjTranspose_mul_self`) the two-site Heisenberg bond
is half the singlet norm-square, hence positive-semidefinite (`x ≠ y`):

* `tJExchangeBond_eq_half_singletNormSq` — `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y = ½ (Δ_xy† Δ_xy)`;
* `tJExchangeBond_posSemidef` — the bond `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y` is positive-semidefinite.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **The Heisenberg bond is half the singlet norm-square** (`x ≠ y`):
`n̂_x n̂_y/4 − Ŝ_x·Ŝ_y = ½ (Δ_xy† Δ_xy)`. -/
theorem tJExchangeBond_eq_half_singletNormSq (x y : Fin (N + 1)) (hxy : x ≠ y) :
    (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) - fermionSpinDot N x y =
      (1 / 2 : ℂ) • ((tJSingletAnnihilation N x y)ᴴ * tJSingletAnnihilation N x y) := by
  rw [tJSingletAnnihilation_conjTranspose_mul_self x y hxy, fermionSiteNumber, fermionSiteNumber,
    fermionSpinDot, fermionSiteSpinZ, fermionSiteSpinZ,
    show fermionUpCreation N x * fermionUpAnnihilation N x = fermionUpNumber N x from rfl,
    show fermionDownCreation N x * fermionDownAnnihilation N x = fermionDownNumber N x from rfl,
    show fermionUpCreation N y * fermionUpAnnihilation N y = fermionUpNumber N y from rfl,
    show fermionDownCreation N y * fermionDownAnnihilation N y = fermionDownNumber N y from rfl]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  match_scalars <;> ring

/-- **The Heisenberg bond is positive-semidefinite** (`x ≠ y`): `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y =
½ Δ_xy† Δ_xy ≥ 0`. -/
theorem tJExchangeBond_posSemidef (x y : Fin (N + 1)) (hxy : x ≠ y) :
    ((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
      fermionSpinDot N x y).PosSemidef := by
  rw [tJExchangeBond_eq_half_singletNormSq x y hxy]
  have hpos : (0 : ℂ) ≤ 1 / 2 := by rw [Complex.le_def]; norm_num
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul hpos

end LatticeSystem.Fermion
