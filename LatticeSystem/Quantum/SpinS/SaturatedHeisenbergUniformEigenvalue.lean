import LatticeSystem.Quantum.SpinS.HeisenbergUniformCasimir
import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace

/-!
# Saturated-FM eigenvalue for uniform J = 1: equals `m_max(m_max + 1)`

For the uniform Heisenberg coupling `J(x, y) = 1`, the
saturated-FM eigenvalue coincides with the Casimir eigenvalue:

  `saturatedFerromagnetEigenvalueS (fun _ _ => 1) N = m_max(m_max + 1)`.

Direct from PR #945 (`H_uniform = Ŝ_tot²`) plus the diagonal entry
of `Ŝ_tot²` at `σ_⊤` (extracted from `(Ŝ_tot)² · |σ_⊤⟩ =
m_max(m_max + 1) · |σ_⊤⟩` evaluated at `σ_⊤`).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `saturatedFerromagnetEigenvalueS (fun _ _ => 1) N =
m_max(m_max + 1)`. -/
theorem saturatedFerromagnetEigenvalueS_uniform [Nonempty V] :
    saturatedFerromagnetEigenvalueS
        (V := V) (fun (_ : V) (_ : V) => (1 : ℂ)) N =
      saturatedFerromagnetCasimirEigenvalueS V N := by
  unfold saturatedFerromagnetEigenvalueS
    saturatedFerromagnetCasimirEigenvalueS
  rw [heisenbergHamiltonianS_uniform_eq_totalSpinSSquared]
  -- Goal: (Ŝ_tot²)(σ_⊤, σ_⊤) = m_max(m_max + 1).
  -- Extract from (Ŝ_tot²) · |σ_⊤⟩ = m_max(m_max + 1) · |σ_⊤⟩ at σ_⊤.
  have h := totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (V := V) (N := N) 0
  simp only [pow_zero, Matrix.one_mulVec] at h
  -- h: Ŝ_tot² · |σ_⊤⟩ = m_max(m_max+1) · |σ_⊤⟩.
  -- Evaluate at σ_⊤: LHS = (Ŝ_tot²)(σ_⊤, σ_⊤) (Matrix.mulVec collapses since
  -- basisVecS σ_⊤ is δ at σ_⊤). RHS = m_max(m_max+1) · 1.
  have h_eval := congrFun h (allAlignedConfigS V N 0)
  unfold allAlignedStateS at h_eval
  rw [show ((totalSpinSSquared V N).mulVec (basisVecS (allAlignedConfigS V N 0)))
        (allAlignedConfigS V N 0) = totalSpinSSquared V N
          (allAlignedConfigS V N 0) (allAlignedConfigS V N 0) from by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (allAlignedConfigS V N 0)]
    · rw [basisVecS_self, mul_one]
    · intros σ _ hσne
      rw [basisVecS_of_ne hσne, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim] at h_eval
  rw [h_eval]
  simp [Pi.smul_apply, basisVecS_self, smul_eq_mul]

end LatticeSystem.Quantum
