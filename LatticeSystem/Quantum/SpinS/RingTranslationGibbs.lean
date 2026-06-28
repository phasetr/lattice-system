/-
Translation invariance of the physical ring Heisenberg Gibbs state
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 38).

Unlike the half-system Marshall gauge (which breaks translations), the physical ring Heisenberg
Hamiltonian `heisenbergHamiltonianS (ringCoupling L)` is translation invariant: the ring translation
`T = chainTranslationOp` commutes with it.  Hence the physical ring Gibbs operator `exp(−β · Ĥ)` is
translation invariant, the partition function is unchanged, and every physical thermal average is
translation covariant — `⟨A⟩ = ⟨T† A T⟩`.  This is the translation symmetry of the thermal state
used by the finite cyclic Fourier / momentum-space analysis of the infrared bound.
-/
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisOrthogonality
import LatticeSystem.Quantum.SpinS.HeisenbergEquilibrium
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace LatticeSystem.Quantum

open Matrix

variable {L N : ℕ}

/-- The ring translation packaged as a unit of the operator ring (with inverse `T`). -/
noncomputable def chainTranslationUnit (L N : ℕ) : (ManyBodyOpS (Fin L) N)ˣ where
  val := (chainTranslationOp L N).conjTranspose
  inv := chainTranslationOp L N
  val_inv := chainTranslationOp_unitary L N
  inv_val := chainTranslationOp_unitary' L N

/-- The underlying operator of `chainTranslationUnit` is `T†`. -/
@[simp] theorem chainTranslationUnit_val :
    (chainTranslationUnit L N : ManyBodyOpS (Fin L) N)
      = (chainTranslationOp L N).conjTranspose := rfl

/-- The underlying operator of `(chainTranslationUnit)⁻¹` is `T`. -/
@[simp] theorem chainTranslationUnit_inv :
    (((chainTranslationUnit L N)⁻¹ : (ManyBodyOpS (Fin L) N)ˣ) : ManyBodyOpS (Fin L) N)
      = chainTranslationOp L N := rfl

/-- Conjugation by the ring translation fixes the physical ring Heisenberg Hamiltonian:
`T† · Ĥ · T = Ĥ`. -/
theorem chainTranslation_conj_heisenbergHamiltonianS (L N : ℕ) :
    (chainTranslationOp L N).conjTranspose * heisenbergHamiltonianS (ringCoupling L) N
        * chainTranslationOp L N
      = heisenbergHamiltonianS (ringCoupling L) N := by
  have h : chainTranslationOp L N * afmHeisenbergChainHamiltonianS L N
      = afmHeisenbergChainHamiltonianS L N * chainTranslationOp L N :=
    chainTranslation_commute_hamiltonian L N
  rw [show heisenbergHamiltonianS (ringCoupling L) N = afmHeisenbergChainHamiltonianS L N from rfl,
    Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, chainTranslationOp_unitary, Matrix.one_mul]

/-- The physical ring Gibbs operator is translation invariant: `T† · exp(−β Ĥ) · T = exp(−β Ĥ)`. -/
theorem chainTranslation_conj_gibbs (L N : ℕ) (β : ℝ) :
    (chainTranslationOp L N).conjTranspose
        * thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling L) N)
        * chainTranslationOp L N
      = thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling L) N) := by
  have h := Matrix.exp_units_conj (chainTranslationUnit L N)
    ((-(β : ℂ)) • heisenbergHamiltonianS (ringCoupling L) N)
  rw [chainTranslationUnit_val, chainTranslationUnit_inv, mul_smul_comm, smul_mul_assoc,
    chainTranslation_conj_heisenbergHamiltonianS] at h
  rw [thermalGibbsOpS]
  exact h.symm

/-- The trace is invariant under conjugation by the ring translation. -/
theorem trace_chainTranslation_conj (X : ManyBodyOpS (Fin L) N) :
    ((chainTranslationOp L N).conjTranspose * X * chainTranslationOp L N).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, chainTranslationOp_unitary', Matrix.one_mul]

/-- **Physical thermal averages are translation covariant**: `⟨T† A T⟩ = ⟨A⟩`. -/
theorem thermalAverageReS_chainTranslation (L N : ℕ) (β : ℝ) (A : ManyBodyOpS (Fin L) N) :
    thermalAverageReS β (heisenbergHamiltonianS (ringCoupling L) N)
        ((chainTranslationOp L N).conjTranspose * A * chainTranslationOp L N)
      = thermalAverageReS β (heisenbergHamiltonianS (ringCoupling L) N) A := by
  rw [thermalAverageReS, thermalAverageReS]
  congr 2
  have hop : (chainTranslationOp L N).conjTranspose * A * chainTranslationOp L N
        * thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling L) N)
      = (chainTranslationOp L N).conjTranspose
        * (A * thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling L) N))
        * chainTranslationOp L N := by
    conv_lhs => rw [← chainTranslation_conj_gibbs L N β]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (chainTranslationOp L N) (chainTranslationOp L N).conjTranspose,
      chainTranslationOp_unitary', Matrix.one_mul]
  rw [hop, trace_chainTranslation_conj]

end LatticeSystem.Quantum
