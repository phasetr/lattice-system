/-
Existence of an eigenvalue strictly above a one-dimensional ground line
(Tasaki §6.2 Theorem 6.3, toward the Lieb–Schultz–Mattis spectral gap).

If a Hermitian matrix on a space of dimension `≥ 2` has its minimum eigenvalue `E₀` realised by a
one-dimensional eigenspace, then some eigenvalue lies strictly above `E₀`: otherwise every eigenvalue
equals `E₀`, forcing `M = E₀ · 1` and hence a full-dimensional `E₀`-eigenspace, contradicting the
one-dimensionality.  This furnishes the first-excited energy `E₁` of the spectral gap.
-/
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Existence of an eigenvalue strictly above a one-dimensional minimum eigenspace.**  For a
Hermitian `M` on a space of dimension `≥ 2` whose minimum eigenvalue `E₀` (so `E₀ ≤ eigenvalues i`
for all `i`) has a one-dimensional eigenspace, some eigenvalue is strictly above `E₀`. -/
theorem hermitian_exists_eigenvalue_gt {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) {E₀ : ℝ} (hcard : 2 ≤ Fintype.card n)
    (hle : ∀ i, E₀ ≤ hM.eigenvalues i)
    (hfin : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' M) (E₀ : ℂ)) ≤ 1) :
    ∃ i, E₀ < hM.eigenvalues i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have heq : ∀ i, hM.eigenvalues i = E₀ := fun i => le_antisymm (h i) (hle i)
  -- `M = E₀ • 1` (spectral decomposition with constant eigenvalues)
  have hM_eq : M = (E₀ : ℂ) • (1 : Matrix n n ℂ) := by
    set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) with hU
    have hspec : M = U * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ))
        * U.conjTranspose := by
      have := hM.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at this
      exact this
    have hdiag : Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ))
        = (E₀ : ℂ) • (1 : Matrix n n ℂ) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
      refine congrArg Matrix.diagonal (funext fun i => ?_)
      rw [heq i, Pi.smul_apply, smul_eq_mul, mul_one]
    have hUUH : U * U.conjTranspose = 1 := eigenvectorUnitary_mul_conjTranspose_eq_one hM
    rw [hspec, hdiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUUH]
  -- the `E₀`-eigenspace of `E₀ • 1` is the whole space
  have htop : Module.End.eigenspace (Matrix.toLin' M) (E₀ : ℂ) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hM_eq, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  -- its finrank is the full dimension `≥ 2`, contradicting `≤ 1`
  rw [htop, finrank_top] at hfin
  have hdim : Module.finrank ℂ (n → ℂ) = Fintype.card n := by simp
  rw [hdim] at hfin
  omega

end LatticeSystem.Quantum
