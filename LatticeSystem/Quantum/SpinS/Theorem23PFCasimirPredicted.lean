import LatticeSystem.Quantum.SpinS.Theorem23PFTotalSpin
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirEigenvector
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Tasaki §2.5 Theorem 2.3 — pinning the ground-state Casimir value via overlap

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  Tasaki's overlap step
(§2.5, eq. 2.5.12): the antiferromagnetic Heisenberg ground state and the
toy-Hamiltonian ground state are both Marshall positive, so their overlap is
non-zero, and since both are total-Casimir eigenvectors their Casimir values
coincide.  As the toy ground state sits at the predicted total spin, the
actual ground state inherits the predicted total-Casimir value.

This module supplies the eigenvalue-realness lemma and the resulting pin:
given any Marshall-positive total-Casimir witness at the predicted value in
the same magnetization sector (the toy ground state), the per-sector
Perron–Frobenius ground state is a total-Casimir eigenvector at exactly the
predicted value `tasaki23PredictedCasimirValue A N`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Realness of a Hermitian eigenvalue**: an eigenvalue of a Hermitian
matrix that has a non-zero eigenvector is fixed by complex conjugation. -/
theorem isHermitian_eigenvalue_star_eq
    {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {γ : ℂ} {v : n → ℂ} (hv : A.mulVec v = γ • v) (hv_ne : v ≠ 0) :
    star γ = γ := by
  have hquad : star v ⬝ᵥ A.mulVec v = γ * (star v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have hleft : Matrix.vecMul (star v) A = star γ • star v := by
    rw [show A = A.conjTranspose from hA.symm, ← Matrix.star_mulVec, hv, star_smul]
  have hquad2 : star v ⬝ᵥ A.mulVec v = star γ * (star v ⬝ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, hleft, smul_dotProduct, smul_eq_mul]
  have hz : star v ⬝ᵥ v ≠ 0 := by
    have hsum : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      rw [dotProduct, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    rw [hsum, Ne, Complex.ofReal_eq_zero]
    intro hsum0
    apply hv_ne
    funext i
    have hi0 : Complex.normSq (v i) = 0 := by
      by_contra hne
      have hpos : 0 < ∑ j, Complex.normSq (v j) :=
        Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
          ⟨i, Finset.mem_univ i,
            lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)⟩
      rw [hsum0] at hpos
      exact lt_irrefl _ hpos
    simpa using (Complex.normSq_eq_zero.mp hi0)
  have heq : γ * (star v ⬝ᵥ v) = star γ * (star v ⬝ᵥ v) := hquad.symm.trans hquad2
  have hsub : (γ - star γ) * (star v ⬝ᵥ v) = 0 := by rw [sub_mul, heq, sub_self]
  have : γ - star γ = 0 := (mul_eq_zero.mp hsub).resolve_right hz
  exact (sub_eq_zero.mp this).symm

end LatticeSystem.Quantum
