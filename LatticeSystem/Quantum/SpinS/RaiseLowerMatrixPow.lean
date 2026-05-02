import LatticeSystem.Quantum.SpinS.RaiseLower
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowPath

/-!
# Matrix-power positivity from raise/lower reachability
(Tasaki §2.5 Phase B-γ γ-3 irreducibility prep)

For the Perron–Frobenius irreducibility step in the spin-S Marshall–
Lieb–Mattis theorem, we lift the combinatorial reachability relation
`RaiseLowerReachableS G σ σ'` to a matrix-power positivity statement.

The key bridge: given a non-negative matrix `B` whose off-diagonal
entries are positive on each `RaiseLowerStepS G σ τ`, then for any
`RaiseLowerReachableS G σ σ'` there exists a power `k` such that
`(B^k) σ' σ > 0`.

This is the spin-S analogue of the spin-1/2 lifting in
`LatticeSystem/Quantum/MarshallLiebMattis/MatrixPowExtend.lean`.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Matrix-power positivity from raise/lower reachability.**

For a non-negative matrix `B` on the configuration space such that
`0 < B τ σ` for every `RaiseLowerStepS G σ τ`, the relation
`RaiseLowerReachableS G σ σ'` lifts to: there exists `k ≥ 1` with
`0 < (B^k) σ' σ`, OR `σ = σ'` (handled by the reflexive case).

The strict version (excluding `σ = σ'`) is captured here by allowing
`k = 0` (`B^0 = 1`, diagonal entry positive) for the reflexive case.

By induction on the `Relation.ReflTransGen` chain. -/
theorem exists_matrixPow_apply_pos_of_raiseLowerReachableS
    {G : SimpleGraph V}
    {B : Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ}
    (hB_nn : ∀ σ τ, 0 ≤ B σ τ)
    (hB_step : ∀ {σ τ : V → Fin (N + 1)},
      RaiseLowerStepS G σ τ → 0 < B τ σ)
    {σ σ' : V → Fin (N + 1)}
    (hreach : RaiseLowerReachableS G σ σ') :
    ∃ k : ℕ, 0 < (B ^ k) σ' σ := by
  induction hreach with
  | refl =>
    -- σ = σ': use k = 0, (B^0) σ σ = 1 > 0.
    refine ⟨0, ?_⟩
    simp [Matrix.one_apply_eq]
  | tail _h₁ h₂ ih =>
    -- σ → ... → τ → σ' (via h₁ : reachable σ τ, h₂ : step τ σ').
    -- IH gives k with (B^k) τ σ > 0. Want (k+1) for (B^(k+1)) σ' σ > 0.
    obtain ⟨k, hpos⟩ := ih
    refine ⟨k + 1, ?_⟩
    -- (B^(k+1)) σ' σ = (B * B^k) σ' σ = ∑_l B σ' l * (B^k) l σ.
    rw [pow_succ', Matrix.mul_apply]
    -- Take l = τ.
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (hB_nn _ _) (Matrix.pow_apply_nonneg hB_nn _ _ _)
    · refine ⟨_, Finset.mem_univ _, mul_pos ?_ hpos⟩
      exact hB_step h₂

end LatticeSystem.Quantum
