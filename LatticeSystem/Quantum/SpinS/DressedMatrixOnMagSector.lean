import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrix
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.RaiseLowerMatrixPow
import LatticeSystem.Math.PerronFrobeniusMain
import LatticeSystem.Math.PerronFrobenius
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

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

/-- **Spin-S Marshall–Lieb–Mattis γ-3 final**: the sector-restricted
shifted dressed Heisenberg matrix is `Matrix.IsIrreducible` under
the standard hypotheses (real symmetric `J` supported on bipartite
bonds, non-negative on each entry, positive on graph edges) plus
strict shift dominance (`c > dressedReMatrix σ σ` for all σ) and the
intermediate-existence hypothesis.

Proof: combines the matrix-power positivity for distinct σ ≠ σ'
(#845) with the diagonal positivity (`M σ σ = c - dressed σ σ > 0`
when `c > dressed σ σ`) via the
`Matrix.isIrreducible_iff_exists_pow_pos` characterization. -/
theorem isIrreducible_shiftedDressedSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn hJ_sym
      hJ_bipartite (fun σ => le_of_lt (hc_strict σ)))]
  intro σ τ
  by_cases hne : σ = τ
  · -- Diagonal: use k = 1, M σ σ = c - dressed σ σ > 0.
    subst hne
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one, shiftedDressedSReMatrixOnMagSector_apply,
      shiftedDressedSReMatrix_apply_diag]
    linarith [hc_strict σ.1]
  · -- Off-diagonal: use #845.
    obtain ⟨k, hk_pos, hpos⟩ :=
      exists_matrixPow_pos_length_of_magConfigS_bipartite A N c hJ_real hJ_pos
        hJ_nn hJ_sym hJ_bipartite (fun σ => le_of_lt (hc_strict σ))
        h_intermediate (Ne.symm hne)
    exact ⟨k, hk_pos, hpos⟩

/-- **Perron–Frobenius for the spin-S dressed Heisenberg matrix**:
under the standard Marshall hypotheses + strict shift dominance +
intermediate-existence, the sector-restricted shifted dressed matrix
admits a Perron eigenvector: there exist a positive eigenvalue `r > 0`
and a strictly positive eigenvector `v > 0` (componentwise) with

    `(shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v`.

Direct corollary of `Matrix.IsIrreducible` (#846) +
`exists_positive_eigenvector_of_irreducible` from the project's
Perron–Frobenius infrastructure. -/
theorem exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (r : ℝ) (v : magConfigS V N M → ℝ),
      0 < r ∧ (∀ σ, 0 < v σ) ∧
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v :=
  LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible
    (isIrreducible_shiftedDressedSReMatrixOnMagSector A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate)

/-- **Uniqueness of the spin-S Perron eigenvector** (γ-3 FINAL): for the
sector-restricted shifted dressed Heisenberg matrix, any two strictly
positive eigenvectors with the same eigenvalue are positive scalar
multiples of each other.

Direct corollary of `Matrix.IsIrreducible` (#846) and
`pos_eigenvec_unique` from PF infrastructure. This is the
non-degeneracy half of Tasaki §2.5 Theorem 2.2 for general spin (the
ground-state in each magnetization sector is unique up to a positive
scalar, equivalently 1-dimensional). -/
theorem pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  LatticeSystem.Math.PerronFrobenius.pos_eigenvec_unique
    (isIrreducible_shiftedDressedSReMatrixOnMagSector A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate)
    hv hv_pos hw hw_pos

/-! ## Dressed Heisenberg sector matrix and its eigenvector -/

/-- The dressed Heisenberg real-matrix restricted to the magnetization-`M`
sector. -/
noncomputable def dressedHeisenbergSReMatrixOnMagSector
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
  (dressedHeisenbergSReMatrix A J N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding of `dressedHeisenbergSReMatrixOnMagSector`. -/
theorem dressedHeisenbergSReMatrixOnMagSector_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    dressedHeisenbergSReMatrixOnMagSector A J N M σ τ =
      dressedHeisenbergSReMatrix A J N σ.1 τ.1 := rfl

/-- The shifted matrix decomposes as `c·1 − dressed` on the sector. -/
theorem shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) (M : ℕ) :
    shiftedDressedSReMatrixOnMagSector A J N c M =
      c • 1 - dressedHeisenbergSReMatrixOnMagSector A J N M := by
  ext σ τ
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    shiftedDressedSReMatrixOnMagSector_apply,
    dressedHeisenbergSReMatrixOnMagSector_apply]
  by_cases hστ : σ = τ
  · subst hστ
    rw [shiftedDressedSReMatrix_apply_diag, Matrix.one_apply_eq]
    ring
  · have hστ' : σ.1 ≠ τ.1 := fun heq => hστ (Subtype.ext heq)
    rw [shiftedDressedSReMatrix_apply_off_diag A J N c hστ',
      Matrix.one_apply_ne hστ]
    ring

/-- Convert an eigenvector of the shifted matrix to an eigenvector of
the dressed matrix (with shifted eigenvalue): if `M_sec v = r v`, then
`dressed_sec v = (c − r) v`. -/
theorem dressedHeisenbergSReMatrixOnMagSector_mulVec_of_shifted_eigenvec
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) {M : ℕ}
    {r : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = (c - r) • v := by
  -- shifted = c•1 - dressed, so dressed = c•1 - shifted.
  -- mulVec linearity:
  -- shifted * v = (c•1 - dressed) * v = c • v - dressed * v.
  -- So r • v = c • v - dressed * v ⟹ dressed * v = (c - r) • v.
  have hdef := shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed A J N c M
  rw [hdef] at hv
  -- hv : (c • 1 - dressed).mulVec v = r • v.
  -- Expand: (c • 1).mulVec v - dressed.mulVec v = r • v.
  -- So dressed.mulVec v = (c • 1).mulVec v - r • v = c • v - r • v = (c - r) • v.
  funext σ
  have hσ := congrFun hv σ
  show (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ = (c - r) * v σ
  -- Compute (c • 1).mulVec v σ = c * v σ.
  have hone : ((c • 1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ) -
      dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
      c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ := by
    rw [Matrix.sub_mulVec]
    show (c • (1 : Matrix _ _ ℝ)).mulVec v σ -
        (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
      c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ
    congr 1
    rw [show (c • (1 : Matrix _ _ ℝ)) = (c : ℝ) • (1 : Matrix _ _ ℝ) from rfl,
      show ((c : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v = c • (1 : Matrix _ _ ℝ).mulVec v
        from Matrix.smul_mulVec _ _ _]
    rw [Matrix.one_mulVec]
    rfl
  rw [hone] at hσ
  show (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ = (c - r) * v σ
  have : (r • v) σ = r * v σ := rfl
  rw [this] at hσ
  linarith

end LatticeSystem.Quantum
