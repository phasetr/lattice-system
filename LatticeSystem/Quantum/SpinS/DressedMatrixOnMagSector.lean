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
  change (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ = (c - r) * v σ
  -- Compute (c • 1).mulVec v σ = c * v σ.
  have hone : ((c • 1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ) -
      dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
      c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ := by
    rw [Matrix.sub_mulVec]
    change (c • (1 : Matrix _ _ ℝ)).mulVec v σ -
        (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
      c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ
    congr 1
    rw [show (c • (1 : Matrix _ _ ℝ)) = (c : ℝ) • (1 : Matrix _ _ ℝ) from rfl,
      show ((c : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v = c • (1 : Matrix _ _ ℝ).mulVec v
        from Matrix.smul_mulVec _ _ _]
    rw [Matrix.one_mulVec]
    rfl
  rw [hone] at hσ
  change (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ = (c - r) * v σ
  have : (r • v) σ = r * v σ := rfl
  rw [this] at hσ
  linarith

/-- **Spin-S Marshall–Lieb–Mattis ground state on the dressed sector
matrix** (γ-3 FINAL THEOREM, dressed form): there exists a strictly
positive eigenvector of the dressed Heisenberg sector matrix, with
eigenvalue `c - r < c` (where `r > 0` is the Perron eigenvalue of
the shifted matrix).

Combines #847 (existence) with #849 (eigenvalue conversion). -/
theorem exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v := by
  obtain ⟨r, v, hr_pos, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector
      (M := M) A N c
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
  refine ⟨c - r, v, by linarith, hv_pos, ?_⟩
  exact dressedHeisenbergSReMatrixOnMagSector_mulVec_of_shifted_eigenvec A J N c
    hmul

/-! ## Heisenberg sector matrix and its eigenvector via Marshall reverse -/

/-- The real-valued Heisenberg matrix restricted to the magnetization-`M`
sector. -/
noncomputable def heisenbergHamiltonianSReMatrixOnMagSector
    (J : V → V → ℂ) (N : ℕ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
  (heisenbergHamiltonianSReMatrix J N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_apply
    (J : V → V → ℂ) (N : ℕ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ =
      heisenbergHamiltonianSReMatrix J N σ.1 τ.1 := rfl

/-- The complex Heisenberg Hamiltonian restricted to the magnetization-`M`
sector (as a complex matrix on the subtype `magConfigS V N M`). -/
noncomputable def heisenbergHamiltonianSMatrixOnMagSector
    (J : V → V → ℂ) (N : ℕ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℂ :=
  (heisenbergHamiltonianS J N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding of the complex sector matrix. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_apply
    (J : V → V → ℂ) (N : ℕ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSMatrixOnMagSector J N M σ τ =
      heisenbergHamiltonianS J N σ.1 τ.1 := rfl

/-- For real coupling, the complex sector matrix entry equals the
real-form sector matrix entry embedded in `ℂ`. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal
    {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSMatrixOnMagSector J N M σ τ =
      ((heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ : ℝ) : ℂ) := by
  rw [heisenbergHamiltonianSMatrixOnMagSector_apply,
    heisenbergHamiltonianSReMatrixOnMagSector_apply,
    heisenbergHamiltonianSReMatrix_apply]
  exact heisenbergHamiltonianS_apply_eq_ofReal_re N hJ_real σ.1 τ.1

/-- For real coupling, the complex Heisenberg sector matrix is
Hermitian (lifted from the full-space Hermiticity). -/
theorem heisenbergHamiltonianSMatrixOnMagSector_isHermitian
    {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).IsHermitian :=
  (heisenbergHamiltonianS_isHermitian_of_real hreal N).submatrix Subtype.val

/-- **Lift a real eigenvector of the real-form sector matrix to a
complex eigenvector of the complex sector matrix**. For real coupling,
if the real-form sector matrix satisfies `M_re v = μ • v`, then the
complex sector matrix satisfies `M_ℂ (v ↑) = μ • (v ↑)` where the
embedding is `(v ↑) σ := (v σ : ℂ)`.

This is the bridge from the PF/MLM real-eigenvector machinery
(PRs #847–#856) to eigenvectors of the actual complex Heisenberg
Hamiltonian on the magnetization sector. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec v = μ • v) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
      (fun σ => (v σ : ℂ)) =
      (μ : ℂ) • (fun σ => (v σ : ℂ)) := by
  funext σ
  have hσ := congrFun hv σ
  -- hσ : ∑ τ, M_re σ τ * v τ = μ * v σ.
  change ∑ τ, heisenbergHamiltonianSMatrixOnMagSector J N M σ τ *
    (v τ : ℂ) = (μ : ℂ) * (v σ : ℂ)
  -- Convert each term from ℂ to ℝ via apply_eq_ofReal.
  have hconv : ∀ τ : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M σ τ * (v τ : ℂ) =
      ((heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * v τ : ℝ) : ℂ) := by
    intro τ
    rw [heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal _ _ hJ_real]
    push_cast
    rfl
  rw [Finset.sum_congr rfl (fun τ _ => hconv τ)]
  rw [← Complex.ofReal_sum]
  change ((heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec v σ : ℂ) =
    (μ : ℂ) * (v σ : ℂ)
  rw [hσ]
  change ((μ * v σ : ℝ) : ℂ) = (μ : ℂ) * (v σ : ℂ)
  push_cast
  ring

/-- **Matrix relation: dressed = sign · sign · heisenberg** (real-part
form). For real coupling, the dressed Heisenberg matrix entry at
`(σ, τ)` equals the product of the Marshall signs at `σ` and `τ` with
the plain Heisenberg matrix entry at `(σ, τ)`. -/
theorem dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ τ =
      (marshallSignS A σ).re * (marshallSignS A τ).re *
        heisenbergHamiltonianSReMatrix J N σ τ := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_def,
    heisenbergHamiltonianSReMatrix_apply]
  -- (sign σ * sign τ * heis σ τ).re = sign σ.re * sign τ.re * heis σ τ.re
  -- since all imaginary parts are 0.
  have hs1 : (marshallSignS A σ).im = 0 := marshallSignS_im A σ
  have hs2 : (marshallSignS A τ).im = 0 := marshallSignS_im A τ
  have hh : (heisenbergHamiltonianS J N σ τ).im = 0 :=
    heisenbergHamiltonianS_apply_im_zero N hJ_real σ τ
  -- Compute the real part of the triple product step by step.
  have h12_re : ((marshallSignS A σ) * (marshallSignS A τ)).re =
      (marshallSignS A σ).re * (marshallSignS A τ).re := by
    rw [Complex.mul_re, hs1]; ring
  have h12_im : ((marshallSignS A σ) * (marshallSignS A τ)).im = 0 := by
    rw [Complex.mul_im, hs1, hs2]; ring
  rw [Complex.mul_re, h12_im, h12_re, hh]
  ring

/-- **Inverse matrix relation: heisenberg = sign · sign · dressed**
(real-part form). Multiplying both sides of the previous lemma by
`sign σ.re * sign τ.re` and using `sign.re² = 1`. -/
theorem heisenbergHamiltonianSReMatrix_eq_marshallSign_mul_dressed
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : V → Fin (N + 1)) :
    heisenbergHamiltonianSReMatrix J N σ τ =
      (marshallSignS A σ).re * (marshallSignS A τ).re *
        dressedHeisenbergSReMatrix A J N σ τ := by
  have h := dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg
    A N hJ_real σ τ
  -- h : dressed = sign σ * sign τ * heis.
  -- Multiply both sides by sign σ * sign τ; LHS becomes (sign σ)² * (sign τ)² * heis = heis.
  have hsq_σ : (marshallSignS A σ).re * (marshallSignS A σ).re = 1 :=
    marshallSignS_re_sq A σ
  have hsq_τ : (marshallSignS A τ).re * (marshallSignS A τ).re = 1 :=
    marshallSignS_re_sq A τ
  -- Apply: sign σ.re * sign τ.re * dressed
  --       = sign σ.re * sign τ.re * (sign σ.re * sign τ.re * heis)
  --       = (sign σ.re)² * (sign τ.re)² * heis = heis.
  rw [h]
  ring_nf
  -- After ring_nf the goal is some polynomial identity in sign.re, sign.re, heis.
  -- We need (sign σ.re)² * (sign τ.re)² * heis = heis.
  -- Use marshallSignS_re_sq.
  calc heisenbergHamiltonianSReMatrix J N σ τ
      = 1 * (1 * heisenbergHamiltonianSReMatrix J N σ τ) := by ring
    _ = ((marshallSignS A σ).re * (marshallSignS A σ).re) *
          (((marshallSignS A τ).re * (marshallSignS A τ).re) *
            heisenbergHamiltonianSReMatrix J N σ τ) := by
          rw [hsq_σ, hsq_τ]
    _ = (marshallSignS A σ).re ^ 2 * (marshallSignS A τ).re ^ 2 *
          heisenbergHamiltonianSReMatrix J N σ τ := by ring

/-- **Marshall-sign-conjugation eigenvector theorem** (Tasaki §2.5
Theorem 2.2 ground-state half, Heisenberg form). Given a real eigenvector
`v` of the dressed Heisenberg sector matrix with eigenvalue `μ`, the
Marshall-sign-conjugated vector

  `w τ := (marshallSignS A τ.1).re * v τ`

is an eigenvector of the (un-dressed) Heisenberg sector matrix with the
same eigenvalue `μ`.

Combined with `exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector`
(γ-3 dressed-form, #850) this gives the Heisenberg-form ground state
on the magnetization sector with the Marshall sign structure. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  funext σ
  -- Goal: (heis_sec).mulVec w σ = μ * w σ where w τ = sign τ.1.re * v τ.
  have hσ := congrFun hv σ
  -- hσ : dressed_sec.mulVec v σ = μ • v σ = μ * v σ.
  change (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun τ => (marshallSignS A τ.1).re * v τ) σ =
    μ * ((marshallSignS A σ.1).re * v σ)
  -- Unfold mulVec to a Finset.sum.
  change ∑ τ, heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ *
      ((marshallSignS A τ.1).re * v τ) =
    μ * ((marshallSignS A σ.1).re * v σ)
  -- Substitute heis = sign · sign · dressed at every term.
  have hsum : ∀ τ : magConfigS V N M,
      heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ *
        ((marshallSignS A τ.1).re * v τ) =
      (marshallSignS A σ.1).re *
        (dressedHeisenbergSReMatrixOnMagSector A J N M σ τ * v τ) := by
    intro τ
    rw [heisenbergHamiltonianSReMatrixOnMagSector_apply,
      dressedHeisenbergSReMatrixOnMagSector_apply,
      heisenbergHamiltonianSReMatrix_eq_marshallSign_mul_dressed A N hJ_real]
    have hsq_τ : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    -- LHS = (sign σ.re * sign τ.re * dressed) * (sign τ.re * v τ)
    --     = sign σ.re * (sign τ.re * sign τ.re) * dressed * v τ
    --     = sign σ.re * 1 * dressed * v τ.
    have key : ((marshallSignS A σ.1).re * (marshallSignS A τ.1).re *
        dressedHeisenbergSReMatrix A J N σ.1 τ.1) *
        ((marshallSignS A τ.1).re * v τ) =
      (marshallSignS A σ.1).re *
        (((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) *
          dressedHeisenbergSReMatrix A J N σ.1 τ.1 * v τ) := by ring
    rw [key, hsq_τ, one_mul]
  rw [Finset.sum_congr rfl (fun τ _ => hsum τ)]
  -- Now: ∑τ sign σ.re * (dressed_sec σ τ * v τ) = μ * (sign σ.re * v σ).
  rw [← Finset.mul_sum]
  -- ∑τ dressed_sec σ τ * v τ = dressed_sec.mulVec v σ.
  change (marshallSignS A σ.1).re *
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    μ * ((marshallSignS A σ.1).re * v σ)
  rw [hσ]
  change (marshallSignS A σ.1).re * (μ * v σ) = μ * ((marshallSignS A σ.1).re * v σ)
  ring

/-- **Spin-S Marshall–Lieb–Mattis ground state on the original Heisenberg
sector matrix** (γ-3 FINAL THEOREM, Heisenberg form): there exists a
NON-ZERO real eigenvector of the (un-dressed) Heisenberg sector matrix
with eigenvalue `μ < c` and the Marshall sign structure
`w τ = (marshallSignS A τ.1).re * (positive function of τ)`.

Composition of:
- `exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector`
  (#850, γ-3 dressed-form): ∃ μ < c, ∃ v > 0, dressed_sec.mulVec v = μ • v.
- `heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec`
  (Marshall-conjugation, this PR).

The eigenvector `w τ := sign A τ.1 .re * v τ` has `|w τ| = v τ > 0`,
so `w` is everywhere non-zero. The sign of `w` matches the Marshall sign
structure. This is the ground-state half of Tasaki §2.5 Theorem 2.2 in
the magnetization sector. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector
      (M := M) A N c
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
      A N hJ_real hmul⟩

/-! ## Inverse Marshall conjugation and uniqueness on the Heisenberg sector -/

/-- **Inverse Marshall conjugation** (heisenberg → dressed): given an
eigenvector `w` of the (un-dressed) Heisenberg sector matrix with
eigenvalue `μ`, the Marshall-conjugated vector `sign · w` is an
eigenvector of the dressed Heisenberg sector matrix with the same
eigenvalue `μ`.

Symmetric to `heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec`,
using the OTHER direction of the matrix relation
`dressed = sign · sign · heis`. -/
theorem dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {w : magConfigS V N M → ℝ}
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec
      (fun σ => (marshallSignS A σ.1).re * w σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * w σ) := by
  funext σ
  have hσ := congrFun hw σ
  change (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec
      (fun τ => (marshallSignS A τ.1).re * w τ) σ =
    μ * ((marshallSignS A σ.1).re * w σ)
  change ∑ τ, dressedHeisenbergSReMatrixOnMagSector A J N M σ τ *
      ((marshallSignS A τ.1).re * w τ) =
    μ * ((marshallSignS A σ.1).re * w σ)
  have hsum : ∀ τ : magConfigS V N M,
      dressedHeisenbergSReMatrixOnMagSector A J N M σ τ *
        ((marshallSignS A τ.1).re * w τ) =
      (marshallSignS A σ.1).re *
        (heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * w τ) := by
    intro τ
    rw [dressedHeisenbergSReMatrixOnMagSector_apply,
      heisenbergHamiltonianSReMatrixOnMagSector_apply,
      dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg A N hJ_real]
    have hsq_τ : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have key : ((marshallSignS A σ.1).re * (marshallSignS A τ.1).re *
        heisenbergHamiltonianSReMatrix J N σ.1 τ.1) *
        ((marshallSignS A τ.1).re * w τ) =
      (marshallSignS A σ.1).re *
        (((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) *
          heisenbergHamiltonianSReMatrix J N σ.1 τ.1 * w τ) := by ring
    rw [key, hsq_τ, one_mul]
  rw [Finset.sum_congr rfl (fun τ _ => hsum τ)]
  rw [← Finset.mul_sum]
  change (marshallSignS A σ.1).re *
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w σ =
    μ * ((marshallSignS A σ.1).re * w σ)
  rw [hσ]
  change (marshallSignS A σ.1).re * (μ * w σ) = μ * ((marshallSignS A σ.1).re * w σ)
  ring

/-- Convert an eigenvector of the dressed matrix to an eigenvector of
the shifted matrix (with shifted eigenvalue): if `dressed_sec v = μ v`,
then `shifted_sec v = (c − μ) v`. (Inverse of #849.) -/
theorem shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) {M : ℕ}
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v) :
    (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = (c - μ) • v := by
  -- shifted = c • 1 - dressed.
  have hdef := shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed A J N c M
  rw [hdef]
  -- Goal: (c • 1 - dressed).mulVec v = (c - μ) • v.
  funext σ
  rw [Matrix.sub_mulVec]
  change (c • (1 : Matrix _ _ ℝ)).mulVec v σ -
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    (c - μ) * v σ
  rw [show ((c : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v =
      c • (1 : Matrix _ _ ℝ).mulVec v from Matrix.smul_mulVec _ _ _,
    Matrix.one_mulVec]
  have hσ := congrFun hv σ
  change c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    (c - μ) * v σ
  have : (μ • v) σ = μ * v σ := rfl
  rw [this] at hσ
  linarith

/-- **Uniqueness of dressed sector eigenvectors at a given eigenvalue**:
any two strictly positive eigenvectors of the dressed Heisenberg sector
matrix with the same eigenvalue `μ` are positive scalar multiples of
each other.

Reduction to `pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector`
(#848): convert both `dressed_sec`-eigenvectors to `shifted_sec`-
eigenvectors at the shifted eigenvalue `c - μ`, then apply PF
uniqueness on the shifted matrix. -/
theorem pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector
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
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v := by
  -- Convert both to shifted-eigenvectors at (c - μ).
  have hv' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hv
  have hw' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hw
  exact pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector A N c
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
    hv' hv_pos hw' hw_pos

/-- **Uniqueness of Marshall-positive Heisenberg sector eigenvectors**
(Tasaki §2.5 Theorem 2.2 nondegeneracy half, Heisenberg form): any two
real eigenvectors `w₁, w₂` of the (un-dressed) Heisenberg sector matrix
at the SAME eigenvalue `μ`, both with strictly positive Marshall-
conjugates `sign · wᵢ > 0`, are positive scalar multiples of each
other.

Reduction: by inverse Marshall conjugation, the conjugates `vᵢ := sign · wᵢ`
are positive eigenvectors of the dressed sector matrix at `μ`. By dressed
sector uniqueness (this PR) `v₂ = r • v₁` for some `r > 0`. Multiplying
both sides by `sign` (which squares to 1) gives `w₂ = r • w₁`. -/
theorem marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
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
    {μ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    ∃ r : ℝ, 0 < r ∧ w₂ = r • w₁ := by
  -- Marshall-conjugate both: vᵢ := sign · wᵢ are dressed eigenvectors.
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₂
  -- Apply dressed uniqueness.
  obtain ⟨r, hr_pos, hrel⟩ :=
    pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector
      A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
      hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos
  -- hrel : (fun σ => sign σ.1.re * w₂ σ) = r • (fun σ => sign σ.1.re * w₁ σ).
  refine ⟨r, hr_pos, ?_⟩
  funext σ
  -- Multiply both sides of hrel σ by sign σ.1.re; sign² = 1 cancels.
  have hσ := congrFun hrel σ
  -- hσ : sign σ.1.re * w₂ σ = r * (sign σ.1.re * w₁ σ).
  change (marshallSignS A σ.1).re * w₂ σ =
    r * ((marshallSignS A σ.1).re * w₁ σ) at hσ
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  -- Multiply both sides by sign σ.1.re.
  have h_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) =
    (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) := by
    rw [hσ]
  -- Simplify both sides via sign² = 1.
  change w₂ σ = r * w₁ σ
  have lhs_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) = w₂ σ := by
    rw [← mul_assoc, hsq, one_mul]
  have rhs_eq : (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) = r * w₁ σ := by
    have : (marshallSignS A σ.1).re *
        (r * ((marshallSignS A σ.1).re * w₁ σ)) =
      ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * (r * w₁ σ) := by
      ring
    rw [this, hsq, one_mul]
  linarith

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), ground-state form
on the magnetization sector**: for the bipartite antiferromagnetic
Heisenberg matrix restricted to the magnetization-`M` sector, there
exists a Marshall-positive ground-state eigenvector `sign · v` (with
`v > 0` componentwise) at some eigenvalue `μ < c`, AND any other
Marshall-positive eigenvector at the SAME eigenvalue `μ` is a positive
scalar multiple of it.

Bundles the existence theorem
(`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`,
PR #853) with the same-eigenvalue uniqueness theorem
(`marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector`,
PR #854) into the form most directly usable downstream. -/
theorem marshallLiebMattis_spinS_heisenbergSector_groundState
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧
      (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) ∧
      (∀ {w : magConfigS V N M → ℝ},
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w →
        (∀ σ, 0 < (marshallSignS A σ.1).re * w σ) →
        ∃ r : ℝ, 0 < r ∧
          w = r • (fun σ => (marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro w hw hw_pos
  have hsign_v_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * v σ) := fun σ => by
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  exact marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
    A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
    hmul hsign_v_pos hw hw_pos

/-! ## Eigenvalue uniqueness (positive eigenvectors share the same eigenvalue) -/

/-- The dressed Heisenberg sector matrix is symmetric (lifted from the
symmetry of the full dressed Heisenberg matrix via `IsSymm.submatrix`). -/
theorem dressedHeisenbergSReMatrixOnMagSector_isSymm
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).IsSymm :=
  (dressedHeisenbergSReMatrix_isSymm A N hreal).submatrix Subtype.val

/-- **Eigenvalue uniqueness for symmetric matrices on positive
eigenvectors**: for a real symmetric matrix `A` over `ℝ`, two strictly
positive eigenvectors with eigenvalues `μ` and `ν` must satisfy `μ = ν`.

Proof: by symmetry `⟨v, A w⟩ = ⟨A v, w⟩`, hence `μ ⟨v, w⟩ = ν ⟨v, w⟩`,
and `⟨v, w⟩ > 0` (positive componentwise sum), so `μ = ν`. -/
theorem pos_eigenvec_eigenvalue_unique_of_isSymm
    {n : Type*} [Fintype n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsSymm)
    {μ ν : ℝ} {v w : n → ℝ}
    (hv : A.mulVec v = μ • v) (hv_pos : ∀ i, 0 < v i)
    (hw : A.mulVec w = ν • w) (hw_pos : ∀ i, 0 < w i) :
    μ = ν := by
  have h_inner_pos : 0 < v ⬝ᵥ w := by
    refine Finset.sum_pos (fun i _ => mul_pos (hv_pos i) (hw_pos i))
      Finset.univ_nonempty
  -- ⟨v, A w⟩ = ν * (v ⬝ᵥ w).
  have h_right : v ⬝ᵥ A.mulVec w = ν * (v ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  -- ⟨v, A w⟩ = ⟨A v, w⟩ by symmetry, then = μ * (v ⬝ᵥ w).
  have hsym : Matrix.vecMul v A = A.mulVec v := by
    funext i
    change ∑ j, v j * A j i = ∑ j, A i j * v j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hAji : A j i = A i j := by
      have hT : A.transpose = A := hA
      have h := congrFun (congrFun hT i) j
      change A j i = A i j at h
      exact h
    rw [hAji, mul_comm]
  have h_left : v ⬝ᵥ A.mulVec w = μ * (v ⬝ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, hsym, hv, smul_dotProduct, smul_eq_mul]
  have h_eq : μ * (v ⬝ᵥ w) = ν * (v ⬝ᵥ w) := by
    rw [← h_left, h_right]
  exact mul_right_cancel₀ (ne_of_gt h_inner_pos) h_eq

/-- **Eigenvalue uniqueness for the dressed Heisenberg sector matrix**:
any two strictly positive eigenvectors with eigenvalues `μ₁, μ₂` must
satisfy `μ₁ = μ₂`. (The dressed sector matrix is symmetric and admits
positive eigenvectors only at the unique Perron eigenvalue.) -/
theorem pos_eigenvec_eigenvalue_unique_dressedHeisenbergSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, star (J x y) = J x y)
    {μ₁ μ₂ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ₁ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ₂ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    μ₁ = μ₂ :=
  pos_eigenvec_eigenvalue_unique_of_isSymm
    (dressedHeisenbergSReMatrixOnMagSector_isSymm A N M hJ_real)
    hv hv_pos hw hw_pos

/-- **Eigenvalue uniqueness for the Heisenberg sector matrix on
Marshall-positive eigenvectors** (Tasaki §2.5 Theorem 2.2 strengthening):
any two real eigenvectors with strictly positive Marshall conjugates
must have the same eigenvalue.

Reduction: by inverse Marshall conjugation (PR #854), the conjugates
`sign · w_i` are positive eigenvectors of the dressed sector matrix
with the same eigenvalues as the heis sector eigenvectors. By dressed
sector eigenvalue uniqueness (this PR) the eigenvalues coincide. -/
theorem marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    {μ₁ μ₂ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ₁ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ₂ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    μ₁ = μ₂ := by
  -- Marshall-conjugate both: vᵢ := sign · wᵢ are dressed positive eigenvectors at μᵢ.
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₂
  exact pos_eigenvec_eigenvalue_unique_dressedHeisenbergSReMatrixOnMagSector
    A N hJ_real' hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), strongest
ground-state form on the magnetization sector**: bundles existence
(PR #853), eigenvector uniqueness at the same eigenvalue (PR #854),
and eigenvalue uniqueness (PR #856) into a single statement of the
form

  ∃ μ < c, ∃ v > 0,
    heis_sec.mulVec (sign · v) = μ • (sign · v) ∧
    ∀ {μ'} {w}, heis_sec.mulVec w = μ' • w → (sign · w > 0) →
      μ' = μ ∧ ∃ r > 0, w = r • (sign · v)

The crucial strengthening over PR #855: the uniqueness clause no
longer requires the comparison eigenvector `w` to be at the SAME `μ`
— eigenvalue uniqueness for Marshall-positive eigenvectors (PR #856)
forces `μ' = μ` automatically. -/
theorem marshallLiebMattis_spinS_heisenbergSector_groundState_full
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧
      (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) ∧
      (∀ {μ' : ℝ} {w : magConfigS V N M → ℝ},
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ' • w →
        (∀ σ, 0 < (marshallSignS A σ.1).re * w σ) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          w = r • (fun σ => (marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro μ' w hw hw_marshall_pos
  -- Marshall-positive `sign · v` is positive (sign² = 1 cancellation).
  have hsign_v_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * v σ) := fun σ => by
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  -- Eigenvalue uniqueness forces μ' = μ.
  have hμ_eq : μ' = μ :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hw hw_marshall_pos hmul hsign_v_pos
  refine ⟨hμ_eq, ?_⟩
  -- Substitute μ' = μ, then apply same-eigenvalue uniqueness (PR #854).
  subst hμ_eq
  exact marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
    A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
    hmul hsign_v_pos hw hw_marshall_pos

end LatticeSystem.Quantum
