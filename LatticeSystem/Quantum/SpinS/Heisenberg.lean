import LatticeSystem.Quantum.SpinS.MultiSiteDot

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

end LatticeSystem.Quantum
