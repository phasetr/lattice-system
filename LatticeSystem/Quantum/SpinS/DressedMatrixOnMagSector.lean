import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrix
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.RaiseLowerMatrixPow

/-!
# Sector-restricted dressed Heisenberg matrix
(Tasaki §2.5 Phase B-γ γ-3 PF prep)

For the spin-S Marshall–Lieb–Mattis theorem via Perron–Frobenius, the
relevant matrix is the dressed Heisenberg matrix RESTRICTED to a single
magnetization-`M` sector (the subtype `magConfigS V N M`). On the full
configuration space the dressed matrix is not irreducible (different
magnetization sectors are disconnected), but each sector restriction is
irreducible (under the bipartite reachability hypothesis).

This module defines the sector-restricted matrix via `Matrix.submatrix`
and proves the basic properties needed for PF.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The shifted dressed Heisenberg matrix restricted to the
magnetization-`M` sector. -/
noncomputable def shiftedDressedSReMatrixOnMagSector
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
  (shiftedDressedSReMatrix A J N c).submatrix Subtype.val Subtype.val

/-- Definitional unfolding of `shiftedDressedSReMatrixOnMagSector`. -/
theorem shiftedDressedSReMatrixOnMagSector_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    shiftedDressedSReMatrixOnMagSector A J N c M σ τ =
      shiftedDressedSReMatrix A J N c σ.1 τ.1 := rfl

/-- Non-negativity of the sector-restricted matrix, lifted from the
non-negativity of `shiftedDressedSReMatrix` (PR #828). -/
theorem shiftedDressedSReMatrixOnMagSector_nonneg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (σ τ : magConfigS V N M) :
    0 ≤ shiftedDressedSReMatrixOnMagSector A J N c M σ τ := by
  rw [shiftedDressedSReMatrixOnMagSector_apply]
  exact shiftedDressedSReMatrix_nonneg A N c hJ_real hJ_nn hJ_sym
    hJ_bipartite hc σ.1 τ.1

/-- The sector-restricted matrix is strictly positive on bipartite
raise/lower steps lifted to the subtype. -/
theorem shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : magConfigS V N M}
    (hstep : RaiseLowerStepSMagSector (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedSReMatrixOnMagSector A J N c M τ σ := by
  rw [shiftedDressedSReMatrixOnMagSector_apply]
  exact shiftedDressedSReMatrix_apply_pos_of_raiseLowerStepS_bipartite A N c
    hJ_real hJ_pos hJ_sym hstep

/-- **Matrix-power positivity from raise/lower reachability on subtype**:
the magConfigS analogue of `exists_matrixPow_apply_pos_of_raiseLowerReachableS`
(PR #815). For a non-negative matrix B on the magConfigS subtype with
0 < B τ σ on every RaiseLowerStepSMagSector σ → τ, the relation
RaiseLowerReachableSMagSector G σ σ' lifts to: there exists k ≥ 0 with
0 < (B^k) σ' σ.

Proof: induction on Relation.ReflTransGen, identical to #815. -/
theorem exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector
    {G : SimpleGraph V} {M : ℕ}
    {B : Matrix (magConfigS V N M) (magConfigS V N M) ℝ}
    (hB_nn : ∀ σ τ, 0 ≤ B σ τ)
    (hB_step : ∀ {σ τ : magConfigS V N M},
      RaiseLowerStepSMagSector G σ τ → 0 < B τ σ)
    {σ σ' : magConfigS V N M}
    (hreach : RaiseLowerReachableSMagSector G σ σ') :
    ∃ k : ℕ, 0 < (B ^ k) σ' σ := by
  induction hreach with
  | refl =>
    refine ⟨0, ?_⟩
    simp [Matrix.one_apply_eq]
  | tail _h₁ h₂ ih =>
    obtain ⟨k, hpos⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (hB_nn _ _) (Matrix.pow_apply_nonneg hB_nn _ _ _)
    · refine ⟨_, Finset.mem_univ _, mul_pos ?_ hpos⟩
      exact hB_step h₂

/-- **Sector-restricted matrix-power positivity** for any pair of
configurations in the same magnetization sector (γ-3 PF irreducibility
input on the subtype). Composition of:
- Bipartite subtype reachability (#841).
- Sector matrix-pow lift from reachability (#843).
- Sector matrix non-negativity (#834).
- Sector matrix step positivity (#842). -/
theorem exists_matrixPow_pos_of_magConfigS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (σ σ' : magConfigS V N M) :
    ∃ k : ℕ, 0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  apply exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector
  · intro σ τ
    exact shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn
      hJ_sym hJ_bipartite hc σ τ
  · intro σ τ hstep
    exact shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector
      A N c M hJ_real hJ_pos hJ_sym hstep
  · exact raiseLowerReachableSMagSector_bipartiteCompleteGraph A
      h_intermediate σ σ'

/-- **Strict positive-length matrix-power positivity** on the sector
for distinct configurations: for σ ≠ σ' in the same sector, the
matrix-power is positive at some k ≥ 1 (excluding the trivial k = 0). -/
theorem exists_matrixPow_pos_length_of_magConfigS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {σ σ' : magConfigS V N M} (hne : σ ≠ σ') :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  obtain ⟨k, hpos⟩ := exists_matrixPow_pos_of_magConfigS_bipartite A N c
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc h_intermediate σ σ'
  refine ⟨k, ?_, hpos⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: (M_sec^0) σ' σ = δ σ' σ = 0 (since σ' ≠ σ).
    subst hk0
    rw [pow_zero, Matrix.one_apply, if_neg (Ne.symm hne)] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hkpos

end LatticeSystem.Quantum
