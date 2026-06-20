import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.ConnectedRaiseLower

/-!
# Connected-graph dressed-matrix Perron–Frobenius positivity
(Tasaki §2.5, Issue #4609 PR2)

The existing γ-3 Perron–Frobenius machinery for the dressed Heisenberg
matrix (`ShiftedDressedMatrix.lean`, `DressedMatrixOnMagSector.lean`,
`Theorem23StructuralReach.lean`) establishes per-magnetization-sector
strict matrix-power positivity for the **complete** bipartite graph
`bipartiteCompleteGraphOf A`.  This file generalises that positivity to
an arbitrary **connected** bipartite graph `G`, so that (in PR3) the
Theorem 2.3 ground-state machinery applies to connected couplings.

The key observation is that a `RaiseLowerStepS G σ τ` exposes a specific
`G`-edge `(x, y)`; under the bipartiteness hypothesis
`hGbip : ∀ x y, G.Adj x y → A x ≠ A y` that edge is cross-sublattice,
so the graph-agnostic step-positivity witness
`neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness`
applies with `hJ_pos_G` evaluated **only at that edge** — we do not need
positivity of `J` on every complete-bipartite bond.  Reachability is
supplied by PR1's `raiseLowerReachableS_of_connected`.

Tracked in #4609.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Strict positivity on connected-graph raise/lower steps -/

/-- **Strict positivity of the shifted dressed matrix on a connected
bipartite-graph raise/lower step.**  For a `RaiseLowerStepS G σ τ` whose
edge is cross-sublattice (guaranteed by `hGbip`), the shifted matrix
entry is strictly positive:

    `0 < shiftedDressedSReMatrix A J N c τ σ`.

Unlike `shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_bipartite`,
this requires positivity of `J` only on the actual `G`-edges
(`hJ_pos_G`), not on every complete-bipartite bond.  The proof unfolds
the step to its witness edge `(x, y)`, uses `hGbip` to get `A x ≠ A y`,
and feeds the graph-agnostic positivity witness
`neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness`. -/
theorem shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_connected
    (A : V → Bool) {G : SimpleGraph V}
    {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {σ τ : V → Fin (N + 1)}
    (hstep : RaiseLowerStepS G σ τ) :
    0 < shiftedDressedSReMatrix A J N c τ σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  -- σ ≠ τ from the step witness (the value at `x` changes).
  have hne : τ ≠ σ := by
    intro heq
    rcases hsh with ⟨hxr, _⟩ | ⟨hxl, _⟩
    · have : (τ x).val = (σ x).val := by rw [heq]
      omega
    · have : (τ x).val = (σ x).val := by rw [heq]
      omega
  -- `A x ≠ A y` from the bipartiteness of `G`.
  have hAne : A x ≠ A y := hGbip x y hadj
  rw [shiftedDressedSReMatrix_apply_off_diag A J N c hne]
  -- `-dressedReMatrix τ σ > 0` from the graph-agnostic positivity witness.
  have hpos : 0 < (-dressedHeisenbergSReMatrix A J N) τ σ :=
    neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness A N
      hadj hAne (hJ_real x y) (hJ_pos_G x y hadj) (hJ_sym x y) hsh hagree
  change 0 < -dressedHeisenbergSReMatrix A J N τ σ at hpos
  linarith

/-- **Sector-restricted strict positivity on a connected bipartite-graph
raise/lower step.**  The `magConfigS`-sector wrapper of
`shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_connected`. -/
theorem shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector_connected
    (A : V → Bool) {G : SimpleGraph V}
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {σ τ : magConfigS V N M}
    (hstep : RaiseLowerStepSMagSector G σ τ) :
    0 < shiftedDressedSReMatrixOnMagSector A J N c M τ σ := by
  rw [shiftedDressedSReMatrixOnMagSector_apply]
  exact shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_connected A N c
    hJ_real hJ_pos_G hJ_sym hGbip hstep

/-! ## Matrix-power positivity for connected bipartite graphs -/

omit [DecidableEq V] in
/-- **Connected-graph sector reachability (PR1 lifted to `magConfigS`).**
For a connected graph `G`, any two configurations in the same
magnetization sector are `RaiseLowerReachableSMagSector`-related,
obtained by lifting `raiseLowerReachableS_of_connected` to the subtype. -/
theorem raiseLowerReachableSMagSector_of_connected
    {G : SimpleGraph V} {M : ℕ}
    (hGconn : G.Connected)
    (σ σ' : magConfigS V N M) :
    RaiseLowerReachableSMagSector G σ σ' := by
  have hreach : RaiseLowerReachableS G σ.1 σ'.1 :=
    raiseLowerReachableS_of_connected G hGconn (σ.2.trans σ'.2.symm)
  exact raiseLowerReachableSMagSector_of_raiseLowerReachableS σ.2 σ'.2 hreach

/-- **Structural matrix-power positivity for a connected bipartite graph.**
The connected-graph analogue of `exists_matrixPow_pos_of_magConfigS_bipartite`:
for any two configurations in the magnetization-`M` sector there is a
power `k` with strictly positive shifted-matrix entry

    `0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ`.

Combines the graph-agnostic sector non-negativity
(`shiftedDressedSReMatrixOnMagSector_nonneg`), the connected step
positivity (this file), and connected reachability (PR1) via the generic
lift `exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector`.

Positivity of `J` is required only on the `G`-edges (`hJ_pos_G`). -/
theorem exists_matrixPow_pos_of_magConfigS_connected
    (A : V → Bool) {G : SimpleGraph V}
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (σ σ' : magConfigS V N M) :
    ∃ k : ℕ, 0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  apply exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector
  · intro σ τ
    exact shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn
      hJ_sym hJ_bipartite hc σ τ
  · intro σ τ hstep
    exact shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector_connected
      A N c M hJ_real hJ_pos_G hJ_sym hGbip hstep
  · exact raiseLowerReachableSMagSector_of_connected hGconn σ σ'

/-- **Strict-positive-length matrix-power positivity for a connected
bipartite graph.**  Mirrors `exists_matrixPow_pos_length_of_magConfigS_bipartite`:
for distinct sector configurations the positive power can be chosen with
`1 ≤ k` (a length-`0` power is the identity, which vanishes off the
diagonal). -/
theorem exists_matrixPow_pos_length_of_magConfigS_connected
    (A : V → Bool) {G : SimpleGraph V}
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    {σ σ' : magConfigS V N M} (hne : σ ≠ σ') :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  obtain ⟨k, hpos⟩ := exists_matrixPow_pos_of_magConfigS_connected A c
    hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc σ σ'
  refine ⟨k, ?_, hpos⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pow_zero, Matrix.one_apply, if_neg (Ne.symm hne)] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hkpos

end LatticeSystem.Quantum
