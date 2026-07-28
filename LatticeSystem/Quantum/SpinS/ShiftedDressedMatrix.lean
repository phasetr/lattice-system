import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrixCore
import LatticeSystem.Quantum.SpinS.RaiseLowerMatrixPow

/-!
# The shifted dressed Heisenberg matrix
(Tasaki §2.5 Phase B-γ γ-3 PF prep)

For Perron–Frobenius application to the dressed Heisenberg matrix, we
need a non-negative matrix derived from `dressedHeisenbergSReMatrix`.
The natural choice is the **shifted negation**:

    `shiftedDressedSReMatrix A J N c := c • 1 - dressedHeisenbergSReMatrix A J N`

For sufficiently large `c` (specifically, `c ≥ max σ, dressedHeisenbergSReMatrix σ σ`):
- Off-diagonal entries are `≥ 0` (since `dressedHeisenbergSReMatrix ≤ 0`
  off-diagonal, by the Marshall sign trick).
- Diagonal entries are `≥ 0` (since `c ≥ dressedHeisenbergSReMatrix σ σ`).

This gives a non-negative matrix to which the standard PF irreducibility
theorem (`exists_positive_eigenvector_of_irreducible`) can be applied.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Matrix-power positivity from raise/lower reachability -/

/-- **Matrix-power positivity from raise/lower reachability** (γ-3 PF
irreducibility input). For the shifted dressed matrix
`shiftedDressedSReMatrix A J N c` (with `c` chosen large enough to
dominate the diagonal), and for any two configurations σ, σ' connected
by a `RaiseLowerReachableS` chain in the bipartite complete graph,
there exists a power `k` such that the matrix-power entry is strictly
positive:

    `0 < (shiftedDressedSReMatrix A J N c ^ k) σ' σ`.

Proof: combines `exists_matrixPow_apply_pos_of_raiseLowerReachableS`
(#815) with the non-negativity (#828) and step-positivity (#829) of
the shifted matrix. -/
theorem exists_matrixPow_pos_of_raiseLowerReachableS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    {σ σ' : V → Fin (N + 1)}
    (hreach : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ') :
    ∃ k : ℕ,
      0 < (shiftedDressedSReMatrix A J N c ^ k) σ' σ := by
  apply exists_matrixPow_apply_pos_of_raiseLowerReachableS
  · -- Non-negativity of the shifted matrix.
    intro σ τ
    exact shiftedDressedSReMatrix_nonneg A N c hJ_real hJ_nn hJ_sym
      hJ_bipartite hc σ τ
  · -- Strict positivity on raise/lower steps.
    intro σ τ hstep
    exact shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_bipartite A N c
      hJ_real hJ_pos hJ_sym hstep
  · exact hreach

/-- **Strictly positive matrix-power** for distinct configurations. For
σ ≠ σ' raise/lower-reachable, the matrix-power positivity holds at
some `k ≥ 1` (excluding the trivial `k = 0` reflexive case which
would give the zero off-diagonal entry).

This is the form needed for `IsSStronglyConnected` of the matrix quiver
(which requires positive-length paths). -/
theorem exists_matrixPow_pos_length_of_raiseLowerReachableS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    {σ σ' : V → Fin (N + 1)} (hne : σ ≠ σ')
    (hreach : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ') :
    ∃ k : ℕ, 1 ≤ k ∧ 0 < (shiftedDressedSReMatrix A J N c ^ k) σ' σ := by
  obtain ⟨k, hpos⟩ := exists_matrixPow_pos_of_raiseLowerReachableS_bipartite A N
    c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc hreach
  -- For k = 0: (M^0) σ' σ = (1) σ' σ = δ σ' σ = 0 (since σ ≠ σ').
  -- So k must be ≥ 1.
  refine ⟨k, ?_, hpos⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: (M^0) σ' σ = δ σ' σ = 0 (since σ ≠ σ'), contradicting hpos > 0.
    subst hk0
    rw [pow_zero, Matrix.one_apply, if_neg (Ne.symm hne)] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hkpos
end LatticeSystem.Quantum
