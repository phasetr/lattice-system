import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.SaturatedFullLadderLI

/-!
# Expectation values of total operators on the all-aligned state

For `[Nonempty V]`, the standard inner product
`⟨v, w⟩ := star v ⬝ᵥ w` (with conjugation on the left) satisfies:

- `⟨|σ_⊤/⊥⟩, |σ_⊤/⊥⟩⟩ = 1` (norm-squared 1).
- `⟨|σ_⊤⟩, Ŝ^z_{tot} |σ_⊤⟩⟩ = m_max` (highest weight).
- `⟨|σ_⊥⟩, Ŝ^z_{tot} |σ_⊥⟩⟩ = -m_max` (lowest weight).
- `⟨|σ_⊤/⊥⟩, (Ŝ_{tot})² |σ_⊤/⊥⟩⟩ = m_max(m_max + 1)` (Casimir).

These expectation values give the explicit `J = m_max` quantum
numbers carried by the saturated-ferromagnet extremal states.
Direct corollaries of PRs #875, #878, #879 (the eigenvector
identities) combined with the orthonormality
`star (basisVecS σ) ⬝ᵥ basisVecS σ = 1`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Norm-squared of `basisVecS` and the all-aligned state -/

/-- The standard basis vector has norm-squared 1:
`star (basisVecS σ) ⬝ᵥ basisVecS σ = 1`. -/
theorem basisVecS_inner_self (σ : V → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (V → Fin (N + 1)) → ℂ))
      (basisVecS σ) = 1 := by
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · -- σ contribution: star 1 * 1 = 1.
    rw [basisVecS_self]
    simp
  · -- τ ≠ σ contribution: 0.
    intros τ _ hτne
    rw [basisVecS_of_ne hτne]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The all-aligned state has norm-squared 1. -/
theorem allAlignedStateS_inner_self (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c)) (allAlignedStateS V N c) = 1 := by
  unfold allAlignedStateS
  exact basisVecS_inner_self _

/-! ## `Ŝ^z_{tot}` expectation values -/

/-- Helper: `⟨v, c • w⟩ = c * ⟨v, w⟩` for `v, w` complex vectors. -/
private theorem dotProduct_smul_right (c : ℂ) (v w : (V → Fin (N + 1)) → ℂ) :
    dotProduct v (c • w) = c * dotProduct v w := by
  rw [dotProduct_smul, smul_eq_mul]

/-- The all-up state has `Ŝ^z_{tot}` expectation value `m_max`. -/
theorem allAlignedStateS_zero_expectation_totalSpinSOp3 :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      ((totalSpinSOp3 V N).mulVec (allAlignedStateS V N (0 : Fin (N + 1)))) =
      (Fintype.card V : ℂ) * (N : ℂ) / 2 := by
  rw [totalSpinSOp3_mulVec_allAlignedStateS, magEigenvalueS_allAlignedConfigS]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
  rw [dotProduct_smul_right, allAlignedStateS_inner_self]
  push_cast; ring

/-- The all-down state has `Ŝ^z_{tot}` expectation value `-m_max`. -/
theorem allAlignedStateS_last_expectation_totalSpinSOp3 :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((totalSpinSOp3 V N).mulVec (allAlignedStateS V N (Fin.last N))) =
      -((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
  rw [totalSpinSOp3_mulVec_allAlignedStateS, magEigenvalueS_allAlignedConfigS]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  rw [dotProduct_smul_right, allAlignedStateS_inner_self]
  push_cast; ring

/-! ## `(Ŝ_{tot})²` expectation values (Casimir) -/

/-- The all-up state has Casimir expectation value `m_max(m_max + 1)`. -/
theorem allAlignedStateS_zero_expectation_totalSpinSSquared
    [Nonempty V] :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      ((totalSpinSSquared V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) := by
  -- Apply Casimir eigenvalue identity (PR #882 at k = 0).
  have h := totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (V := V) (N := N) 0
  simp only [pow_zero, Matrix.one_mulVec] at h
  rw [h, dotProduct_smul_right, allAlignedStateS_inner_self]
  ring

/-- The all-down state has Casimir expectation value `m_max(m_max + 1)`. -/
theorem allAlignedStateS_last_expectation_totalSpinSSquared
    [Nonempty V] :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((totalSpinSSquared V N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) := by
  have h := totalSpinSSquared_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    (V := V) (N := N) 0
  simp only [pow_zero, Matrix.one_mulVec] at h
  rw [h, dotProduct_smul_right, allAlignedStateS_inner_self]
  ring

/-! ## `(Ŝ_{tot}^{(3)})²` expectation values (γ-4 step 202) -/

/-- Helper: `(Ŝ_tot^{(3)})²` acts on the all-aligned state at `c` as
multiplication by the squared eigenvalue `(magEigenvalueS c)²`. -/
private theorem totalSpinSOp3_sq_mulVec_allAlignedStateS (c : Fin (N + 1)) :
    (totalSpinSOp3 V N * totalSpinSOp3 V N).mulVec (allAlignedStateS V N c) =
      (magEigenvalueS (allAlignedConfigS V N c)) ^ 2 •
        allAlignedStateS V N c := by
  rw [← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
    Matrix.mulVec_smul, totalSpinSOp3_mulVec_allAlignedStateS,
    smul_smul]
  ring_nf

/-- `(Ŝ_tot^{(3)})²` expectation on the all-aligned state at `c` equals
`(magEigenvalueS c)² = (|V|·N/2 - |V|·c)²` (γ-4 step 202). -/
theorem allAlignedStateS_expectation_totalSpinSOp3_sq (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
        ((totalSpinSOp3 V N * totalSpinSOp3 V N).mulVec
          (allAlignedStateS V N c)) =
      (magEigenvalueS (allAlignedConfigS V N c)) ^ 2 := by
  rw [totalSpinSOp3_sq_mulVec_allAlignedStateS,
    dotProduct_smul_right, allAlignedStateS_inner_self, mul_one]

/-- All-up specialisation of γ-4 step 202: `(Ŝ_tot^{(3)})²` expectation
equals `(|V|·N/2)²`. -/
theorem allAlignedStateS_zero_expectation_totalSpinSOp3_sq :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
        ((totalSpinSOp3 V N * totalSpinSOp3 V N).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) ^ 2 := by
  rw [allAlignedStateS_expectation_totalSpinSOp3_sq,
    magEigenvalueS_allAlignedConfigS]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
  ring

/-- All-down specialisation of γ-4 step 202: `(Ŝ_tot^{(3)})²` expectation
equals `(|V|·N/2)²` (the lowest weight has eigenvalue `-|V|·N/2`, whose
square coincides with the highest-weight square). -/
theorem allAlignedStateS_last_expectation_totalSpinSOp3_sq :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
        ((totalSpinSOp3 V N * totalSpinSOp3 V N).mulVec
          (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) ^ 2 := by
  rw [allAlignedStateS_expectation_totalSpinSOp3_sq,
    magEigenvalueS_allAlignedConfigS]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  ring

end LatticeSystem.Quantum
