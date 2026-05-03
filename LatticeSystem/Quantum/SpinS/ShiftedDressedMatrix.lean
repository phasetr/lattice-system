import LatticeSystem.Quantum.SpinS.DressedHeisenberg
import LatticeSystem.Quantum.SpinS.DressedHeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph
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
