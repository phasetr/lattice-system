/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 4 — assembly.

Combines the renormalized denominator bound (Lemma R1) and the renormalized numerator bound
(Lemma R2, via the variational double-commutator identity) to discharge the energy-bound axiom
`tower_lowLying_energy_bound`.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-! ### Variational identity feeders (P9-6) -/

/-- A Hermitian matrix has real eigenvalues: an eigenvalue `E₀` with a nonzero eigenvector
(`H Φ = E₀ Φ`) has `E₀.im = 0`. -/
theorem hermitian_mulVec_eigenvalue_im_zero {n : Type*} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {Φ : n → ℂ} {E₀ : ℂ}
    (hΦ : Φ ≠ 0) (hev : H.mulVec Φ = E₀ • Φ) : E₀.im = 0 := by
  have hnn : (0 : ℂ) ≤ star Φ ⬝ᵥ Φ := dotProduct_star_self_nonneg Φ
  have hpos : (0 : ℂ) < star Φ ⬝ᵥ Φ := Matrix.dotProduct_star_self_pos_iff.mpr hΦ
  have hΦim : (star Φ ⬝ᵥ Φ).im = 0 := ((Complex.le_def.mp hnn).2).symm
  have hΦre : 0 < (star Φ ⬝ᵥ Φ).re := (Complex.lt_def.mp hpos).1
  have him : (star Φ ⬝ᵥ H.mulVec Φ).im = 0 := hermitian_dotProduct_im_zero hH Φ
  rw [hev, dotProduct_smul, smul_eq_mul, Complex.mul_im, hΦim, mul_zero, zero_add] at him
  exact (mul_eq_zero.mp him).resolve_right (ne_of_gt hΦre)

/-- The torus nearest-neighbor coupling is real-valued (`0` or `1`). -/
theorem torusNNCoupling_real (d L : ℕ) [NeZero L] (x y : HypercubicTorus d L) :
    star (torusNNCoupling d L x y) = torusNNCoupling d L x y := by
  unfold torusNNCoupling
  classical
  split <;> simp

/-- The torus AFM Heisenberg Hamiltonian is Hermitian. -/
theorem heisenbergHamiltonianS_torus_isHermitian (d L N : ℕ) [NeZero L] :
    (heisenbergHamiltonianS (torusNNCoupling d L) N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real (torusNNCoupling_real d L) N

end LatticeSystem.Quantum
