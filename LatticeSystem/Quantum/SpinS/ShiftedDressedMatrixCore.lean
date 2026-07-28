import LatticeSystem.Quantum.SpinS.DressedHeisenberg
import LatticeSystem.Quantum.SpinS.DressedHeisenbergMarshall
import LatticeSystem.Quantum.SpinS.DressedHeisenbergOffXY
import LatticeSystem.Quantum.SpinS.DressedHeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphCore

/-!
# Shifted dressed Heisenberg matrix: non-negativity and strict positivity (foundation)

Foundational layer extracted from `ShiftedDressedMatrix.lean` for build speed.  This file
defines the shifted dressed matrix and proves its entrywise non-negativity and its strict
positivity on bipartite raise/lower steps.

The matrix-power positivity from raise/lower reachability is kept in the capstone module
`ShiftedDressedMatrix.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}


/-- The shifted negation of the dressed Heisenberg real-matrix:

    `shiftedDressedSReMatrix A J N c := c • 1 − dressedHeisenbergSReMatrix A J N`.

For `c` large enough, this matrix is non-negative everywhere and
strictly positive on bipartite raise/lower steps — the form needed
for Perron–Frobenius irreducibility on the magnetization subspace. -/
noncomputable def shiftedDressedSReMatrix
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) :
    Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ :=
  c • 1 - dressedHeisenbergSReMatrix A J N

/-- Definitional unfolding of `shiftedDressedSReMatrix`. -/
theorem shiftedDressedSReMatrix_def
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) :
    shiftedDressedSReMatrix A J N c =
      c • 1 - dressedHeisenbergSReMatrix A J N := rfl

/-- Off-diagonal entry of the shifted dressed matrix:
`shiftedDressedSReMatrix σ' σ = -dressedHeisenbergSReMatrix σ' σ`
(for `σ' ≠ σ`, the diagonal contribution `c · 1` vanishes). -/
theorem shiftedDressedSReMatrix_apply_off_diag
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    shiftedDressedSReMatrix A J N c σ' σ =
      -dressedHeisenbergSReMatrix A J N σ' σ := by
  unfold shiftedDressedSReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- Diagonal entry of the shifted dressed matrix:
`shiftedDressedSReMatrix σ σ = c − dressedHeisenbergSReMatrix σ σ`. -/
theorem shiftedDressedSReMatrix_apply_diag
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ)
    (σ : V → Fin (N + 1)) :
    shiftedDressedSReMatrix A J N c σ σ =
      c - dressedHeisenbergSReMatrix A J N σ σ := by
  unfold shiftedDressedSReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]

/-! ## Non-negativity -/

/-- **Off-diagonal non-negativity of the shifted dressed matrix**:
under the standard Marshall-trick hypotheses (real symmetric `J`
supported on bipartite bonds, non-negative on each entry), the
off-diagonal entries of `shiftedDressedSReMatrix` are `≥ 0` (any
shift `c` works). -/
theorem shiftedDressedSReMatrix_apply_off_diag_nonneg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    0 ≤ shiftedDressedSReMatrix A J N c σ' σ := by
  rw [shiftedDressedSReMatrix_apply_off_diag A J N c hne]
  -- -dressedReMatrix ≥ 0 iff dressedReMatrix ≤ 0.
  -- dressedReMatrix σ' σ = (dressedHeisenbergS σ' σ).re.
  -- By #799, (dressedHeisenbergS σ' σ).re ≤ 0 for σ' ≠ σ.
  have hnonpos : (dressedHeisenbergS A J N σ' σ).re ≤ 0 :=
    dressedHeisenbergS_apply_re_nonpos_of_ne_bipartite A N hJ_real hJ_nn
      hJ_sym hJ_bipartite hne
  rw [dressedHeisenbergSReMatrix_apply]
  linarith

/-- **Diagonal non-negativity** of the shifted dressed matrix when the
shift `c` dominates the diagonal: `c ≥ dressedReMatrix σ σ` gives
`shiftedDressedSReMatrix σ σ ≥ 0`. -/
theorem shiftedDressedSReMatrix_apply_diag_nonneg
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ)
    (σ : V → Fin (N + 1))
    (hc : dressedHeisenbergSReMatrix A J N σ σ ≤ c) :
    0 ≤ shiftedDressedSReMatrix A J N c σ σ := by
  rw [shiftedDressedSReMatrix_apply_diag]
  linarith

/-- **Full non-negativity of the shifted dressed matrix**: combines
off-diagonal and diagonal non-negativity. Requires the standard
Marshall-trick hypotheses on `J` AND the diagonal-dominance shift
`c ≥ max σ, dressedReMatrix σ σ`. -/
theorem shiftedDressedSReMatrix_nonneg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (σ' σ : V → Fin (N + 1)) :
    0 ≤ shiftedDressedSReMatrix A J N c σ' σ := by
  by_cases hne : σ' = σ
  · subst hne
    exact shiftedDressedSReMatrix_apply_diag_nonneg A J N c σ' (hc σ')
  · exact shiftedDressedSReMatrix_apply_off_diag_nonneg A N c hJ_real hJ_nn
      hJ_sym hJ_bipartite hne

/-! ## Strict positivity on bipartite raise/lower steps -/

/-- **Strict positivity of the shifted dressed matrix on bipartite
raise/lower steps**: for a `RaiseLowerStepS` in the bipartite complete
graph (so σ ≠ τ automatically and witness sites are bipartite), the
shifted matrix entry is strictly positive:

    `0 < shiftedDressedSReMatrix A J N c τ σ`.

Proof: off-diagonal formula reduces to `-dressedReMatrix τ σ`, which
is positive by #826. -/
theorem shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : V → Fin (N + 1)}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedSReMatrix A J N c τ σ := by
  -- σ ≠ τ from the step witness (changes the value at x or y).
  have hne : τ ≠ σ := by
    obtain ⟨x, y, _hadj, hsh, _hagree⟩ := hstep
    intro heq
    rcases hsh with ⟨hxr, _⟩ | ⟨hxl, _⟩
    · have : (τ x).val = (σ x).val := by rw [heq]
      omega
    · have : (τ x).val = (σ x).val := by rw [heq]
      omega
  rw [shiftedDressedSReMatrix_apply_off_diag A J N c hne]
  exact neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_bipartite A
    N hJ_real hJ_pos hJ_sym hstep

end LatticeSystem.Quantum
