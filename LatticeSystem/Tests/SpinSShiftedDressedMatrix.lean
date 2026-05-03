import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrix

/-!
# Test coverage for the spin-`S` shifted dressed Heisenberg matrix
(Tasaki §2.5 Phase B-γ γ-3 PF prep)
-/

namespace LatticeSystem.Tests.SpinSShiftedDressedMatrix

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definitional unfolding. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ) (c : ℝ) :
    shiftedDressedSReMatrix A J N c =
      c • 1 - dressedHeisenbergSReMatrix A J N :=
  shiftedDressedSReMatrix_def A J N c

/-- Off-diagonal entry: `-dressedReMatrix σ' σ`. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ) (c : ℝ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    shiftedDressedSReMatrix A J N c σ' σ =
      -dressedHeisenbergSReMatrix A J N σ' σ :=
  shiftedDressedSReMatrix_apply_off_diag A J N c hne

/-- Diagonal entry: `c - dressedReMatrix σ σ`. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ) (c : ℝ)
    (σ : V → Fin (N + 1)) :
    shiftedDressedSReMatrix A J N c σ σ =
      c - dressedHeisenbergSReMatrix A J N σ σ :=
  shiftedDressedSReMatrix_apply_diag A J N c σ

/-- Off-diagonal non-negativity (under standard Marshall hypotheses). -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    0 ≤ shiftedDressedSReMatrix A J N c σ' σ :=
  shiftedDressedSReMatrix_apply_off_diag_nonneg A N c hJ_real hJ_nn hJ_sym
    hJ_bipartite hne

/-- Full non-negativity (when c dominates the diagonal). -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (σ' σ : V → Fin (N + 1)) :
    0 ≤ shiftedDressedSReMatrix A J N c σ' σ :=
  shiftedDressedSReMatrix_nonneg A N c hJ_real hJ_nn hJ_sym hJ_bipartite hc σ' σ

/-- Strict positivity on bipartite raise/lower step. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : V → Fin (N + 1)}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedSReMatrix A J N c τ σ :=
  shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_bipartite A N c
    hJ_real hJ_pos hJ_sym hstep

/-- Matrix-power positivity from raise/lower reachability — the
γ-3 PF irreducibility input. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    {σ σ' : V → Fin (N + 1)}
    (hreach : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ') :
    ∃ k : ℕ,
      0 < (shiftedDressedSReMatrix A J N c ^ k) σ' σ :=
  exists_matrixPow_pos_of_raiseLowerReachableS_bipartite A N c hJ_real hJ_pos
    hJ_nn hJ_sym hJ_bipartite hc hreach

end LatticeSystem.Tests.SpinSShiftedDressedMatrix
