import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Expectation values on saturated-ferromagnet ladder iterates

For each iterate `v_k := (Ŝ^-_{tot})^k · |σ_⊤⟩`, the relevant
expectation values are scalar multiples of the squared norm
`⟨v_k, v_k⟩`:

- `⟨v_k, Ŝ^z_{tot} · v_k⟩ = (m_max - k) · ⟨v_k, v_k⟩`.
- `⟨v_k, Ŝ_{tot}² · v_k⟩ = m_max(m_max + 1) · ⟨v_k, v_k⟩`.
- `⟨v_k, H · v_k⟩ = c_J · ⟨v_k, v_k⟩`.

Direct corollaries of the eigenvalue identities (PRs #881, #882,
#887) combined with `dotProduct_smul`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `⟨v_k, Ŝ^z_{tot} · v_k⟩ = (m_max - k) · ⟨v_k, v_k⟩`. -/
theorem ladderIterateUp_expectation_totalSpinSOp3
    (k : Fin (Fintype.card V * N + 1)) :
    dotProduct (star (ladderIterateUp V N k))
      ((totalSpinSOp3 V N).mulVec (ladderIterateUp V N k)) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) *
        dotProduct (star (ladderIterateUp V N k)) (ladderIterateUp V N k) := by
  unfold ladderIterateUp
  rw [totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero]
  rw [dotProduct_smul, smul_eq_mul]

/-- `⟨v_k, Ŝ_{tot}² · v_k⟩ = m_max(m_max + 1) · ⟨v_k, v_k⟩`. -/
theorem ladderIterateUp_expectation_totalSpinSSquared
    [Nonempty V] (k : Fin (Fintype.card V * N + 1)) :
    dotProduct (star (ladderIterateUp V N k))
      ((totalSpinSSquared V N).mulVec (ladderIterateUp V N k)) =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) *
        dotProduct (star (ladderIterateUp V N k)) (ladderIterateUp V N k) := by
  unfold ladderIterateUp
  rw [totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero]
  rw [dotProduct_smul, smul_eq_mul]

/-- `⟨v_k, H · v_k⟩ = c_J · ⟨v_k, v_k⟩`. -/
theorem ladderIterateUp_expectation_heisenbergHamiltonianS
    (J : V → V → ℂ) (k : Fin (Fintype.card V * N + 1)) :
    dotProduct (star (ladderIterateUp V N k))
      ((heisenbergHamiltonianS J N).mulVec (ladderIterateUp V N k)) =
      (saturatedFerromagnetEigenvalueS (V := V) J N) *
        dotProduct (star (ladderIterateUp V N k)) (ladderIterateUp V N k) := by
  unfold ladderIterateUp saturatedFerromagnetEigenvalueS
  rw [heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero]
  rw [dotProduct_smul, smul_eq_mul]

end LatticeSystem.Quantum
