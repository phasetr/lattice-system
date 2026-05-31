import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.Op3Square
import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement
import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag

/-!
# Off-diagonal agreement of the anisotropic and isotropic Heisenberg Hamiltonians

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

In Tasaki's Hamiltonian (2.5.14) the anisotropy `λ` multiplies only the
longitudinal term `Ŝ_x⁽³⁾Ŝ_y⁽³⁾` and the crystal field `D` only the single-ion
term `(Ŝ_x⁽³⁾)²`.  Both are built from the **diagonal** operator `Ŝ⁽³⁾`, so the
difference

  `anisotropicHeisenbergS J λ D N − heisenbergHamiltonianS J N`

is a diagonal many-body matrix.  Consequently the two Hamiltonians have
**identical off-diagonal entries** (`σ' ≠ σ`).  This is the structural fact that
lets the balanced-magnetization-sector Perron–Frobenius route for Theorem 2.4
reuse the isotropic off-diagonal sign/support analysis for the whole range
`−1 < λ < 1` (in particular without a `λ' ≤ 0` sign obstruction, since the
off-diagonal does not depend on `λ` at all).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43 (equation (2.5.14)).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The same-site square `Ŝ_x⁽³⁾ Ŝ_x⁽³⁾` is diagonal: it vanishes off the diagonal
of the many-body configuration space. -/
theorem onSiteS_spinSOp3_sq_apply_eq_zero_of_ne
    (x : Λ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_same, onSiteS_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    by_cases hx : σ' x = σ x
    · exact absurd (funext fun k => by
        by_cases hk : k = x
        · rw [hk]; exact hx
        · exact h k hk) hne
    · rw [spinSOp3_sq_eq_diagonal, Matrix.diagonal_apply_ne _ hx]
  · rw [if_neg h]

/-- The single-ion anisotropy term `D Σ_x (Ŝ_x⁽³⁾)²` vanishes off the diagonal. -/
theorem singleIonAnisotropyS_apply_offdiag_eq_zero
    (D : ℂ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (singleIonAnisotropyS (Λ := Λ) D N) σ' σ = 0 := by
  rw [singleIonAnisotropyS, Matrix.smul_apply, Matrix.sum_apply,
    Finset.sum_eq_zero (fun x _ => onSiteS_spinSOp3_sq_apply_eq_zero_of_ne x hne),
    smul_zero]

/-- **XXZ off-diagonal agrees with the isotropic dot**: for `σ' ≠ σ` the XXZ bond
term and the isotropic two-site dot term have identical entries, because the
anisotropy multiplies only the diagonal `Ŝ³Ŝ³` part. -/
theorem spinSDotXXZ_apply_offdiag_eq_spinSDot
    (x y : Λ) (lam : ℂ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    spinSDotXXZ x y lam N σ' σ = spinSDot x y N σ' σ := by
  rw [spinSDotXXZ_def, spinSDot_def, Matrix.add_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.add_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [onSiteS_spinSOp3_sq_apply_eq_zero_of_ne x hne, smul_zero]
  · rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, smul_zero]

/-- **Off-diagonal agreement**: for `σ' ≠ σ` the anisotropic Heisenberg
Hamiltonian and the isotropic Heisenberg Hamiltonian have identical entries. -/
theorem anisotropicHeisenbergS_apply_offdiag_eq_heisenberg
    (J : Λ → Λ → ℂ) (lam D : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    anisotropicHeisenbergS (Λ := Λ) J lam D N σ' σ =
      heisenbergHamiltonianS J N σ' σ := by
  rw [anisotropicHeisenbergS_def, heisenbergHamiltonianS_def, Matrix.add_apply,
    singleIonAnisotropyS_apply_offdiag_eq_zero D hne, add_zero,
    Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.smul_apply, Matrix.smul_apply,
    spinSDotXXZ_apply_offdiag_eq_spinSDot x y lam hne]

end LatticeSystem.Quantum
