import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.TotalSquared

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

/-- The Heisenberg Hamiltonian commutes with the Casimir `(Ŝ_tot)²`:
operator-level SU(2) invariance at the Casimir level. Follows from
`[Ĥ_J, Ŝ_tot^{(α)}] = 0` for each axis (β-3o) via `Commute.mul_right`
and `Commute.add_right`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSSquared
    (J : Λ → Λ → ℂ) (N : ℕ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSSquared Λ N) := by
  unfold totalSpinSSquared
  have h1 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp1 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp1 J N)
  have h2 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp2 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp2 J N)
  have h3 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp3 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp3 J N)
  exact ((h1.mul_right h1).add_right (h2.mul_right h2)).add_right
    (h3.mul_right h3)

/-- The Heisenberg Hamiltonian preserves `(Ŝ_tot)²` eigenvalues:
if `(Ŝ_tot)² · v = S · v`, then `(Ŝ_tot)² · (Ĥ · v) = S · (Ĥ · v)`.
Operator-level simultaneous diagonalisation. -/
theorem heisenbergHamiltonianS_mulVec_preserves_totalSpinSSquared_eigenvalue
    (J : Λ → Λ → ℂ) (N : ℕ)
    {S : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : (totalSpinSSquared Λ N).mulVec v = S • v) :
    (totalSpinSSquared Λ N).mulVec
        ((heisenbergHamiltonianS J N).mulVec v) =
      S • (heisenbergHamiltonianS J N).mulVec v := by
  have hcomm : totalSpinSSquared Λ N * heisenbergHamiltonianS J N =
      heisenbergHamiltonianS J N * totalSpinSSquared Λ N :=
    (heisenbergHamiltonianS_commute_totalSpinSSquared J N).symm
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

end LatticeSystem.Quantum
