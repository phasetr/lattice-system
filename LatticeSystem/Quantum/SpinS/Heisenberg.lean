import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` Heisenberg-type Hamiltonian
(Tasaki §2.5 Phase B-β β-3h)

The general Heisenberg-type Hamiltonian on the multi-site spin-`S`
Hilbert space:

  `Ĥ_J := Σ_{x, y : Λ} J(x, y) • Ŝ_x · Ŝ_y`.

This is the spin-`S` analogue of `heisenbergHamiltonian`
(`Quantum/SpinDot/Hamiltonian.lean`) and the foundation for the
single-cluster (Problem 2.5.a) and Marshall–Lieb–Mattis (Theorem 2.2)
machinery for general spin (Issue #412 Phase B-γ).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The spin-`S` Heisenberg-type Hamiltonian on `Λ` with coupling
`J : Λ → Λ → ℂ`. -/
noncomputable def heisenbergHamiltonianS (J : Λ → Λ → ℂ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  ∑ x : Λ, ∑ y : Λ, J x y • spinSDot x y N

/-- A spin-`S` Heisenberg Hamiltonian with **real** coupling
(`star (J x y) = J x y`) is Hermitian. No symmetry of `J` is needed,
since `Ŝ_x · Ŝ_y` is always Hermitian (β-3g) — symmetry of the
coupling is automatically symmetrised by the doubled sum
`∑_{x, y} J(x, y) Ŝ_x · Ŝ_y`. -/
theorem heisenbergHamiltonianS_isHermitian_of_real
    {J : Λ → Λ → ℂ} (hreal : ∀ x y, star (J x y) = J x y) (N : ℕ) :
    (heisenbergHamiltonianS (Λ := Λ) J N).IsHermitian := by
  unfold heisenbergHamiltonianS Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  congr 1; funext x
  rw [Matrix.conjTranspose_sum]
  congr 1; funext y
  rw [Matrix.conjTranspose_smul, (spinSDot_isHermitian x y N).eq]
  rw [hreal]

/-! ## SU(2) invariance (Tasaki §2.2 (2.2.13) general S) -/

/-- SU(2) invariance, axis 1: the spin-`S` Heisenberg Hamiltonian
commutes with `Ŝ_tot^{(1)}`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp1
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp1, smul_zero]

/-- SU(2) invariance, axis 2: `[Ĥ_J, Ŝ_tot^{(2)}] = 0`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp2
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp2, smul_zero]

/-- SU(2) invariance, axis 3: `[Ĥ_J, Ŝ_tot^{(3)}] = 0`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp3
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp3, smul_zero]

end LatticeSystem.Quantum
