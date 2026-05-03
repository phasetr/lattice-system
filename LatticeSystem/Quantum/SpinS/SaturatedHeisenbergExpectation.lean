import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Heisenberg expectation on the saturated-ferromagnet states

For the saturated-ferromagnet states `|σ_⊤⟩` and `|σ_⊥⟩`, the
Heisenberg expectation value equals
`saturatedFerromagnetEigenvalueS J N` (the H diagonal at the
all-up configuration):

  `⟨|σ_⊤⟩, H · |σ_⊤⟩⟩ = saturatedFerromagnetEigenvalueS J N`,
  `⟨|σ_⊥⟩, H · |σ_⊥⟩⟩ = saturatedFerromagnetEigenvalueS J N`.

(For symmetric `J` the all-up and all-down states share the same
H-eigenvalue by Tasaki §2.4.)

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `⟨|σ_⊤⟩, H · |σ_⊤⟩⟩ = saturatedFerromagnetEigenvalueS J N`. -/
theorem allAlignedStateS_zero_expectation_heisenbergHamiltonianS
    (J : V → V → ℂ) :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      ((heisenbergHamiltonianS J N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      saturatedFerromagnetEigenvalueS (V := V) J N := by
  have h_eig := heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (V := V) (N := N) J 0
  simp only [pow_zero, Matrix.one_mulVec] at h_eig
  unfold saturatedFerromagnetEigenvalueS
  rw [h_eig]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

/-- `⟨|σ_⊥⟩, H · |σ_⊥⟩⟩ = H(σ_⊥, σ_⊥)` (the all-down H-diagonal).

For symmetric `J`, `H(σ_⊥, σ_⊥) = H(σ_⊤, σ_⊤)` so both extremal
states share the same H-eigenvalue, but at the operator-level this
PR keeps the two distinct expressions; the equality requires
extra symmetry. -/
theorem allAlignedStateS_last_expectation_heisenbergHamiltonianS
    (J : V → V → ℂ) :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((heisenbergHamiltonianS J N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N)) := by
  have h_eig := heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    (V := V) (N := N) J 0
  simp only [pow_zero, Matrix.one_mulVec] at h_eig
  rw [h_eig]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

end LatticeSystem.Quantum
