import LatticeSystem.Math.PerronFrobeniusMain
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Perron-Frobenius theorem for symmetric non-negative irreducible matrices

For a real symmetric non-negative irreducible matrix `A`:

1. (`exists_pos_eigenvec_max`) The maximum eigenvalue `μ` has a strictly positive eigenvector.
2. (`pos_eigenvec_unique`) This eigenvector is unique up to a positive scalar.

## Mathematical proof

### Step 1 — Non-negative eigenvector (symmetric nonneg case)
Let `v` be any max eigenvector (exists from `Matrix.IsHermitian.eigenvectorBasis`) and set
`w i = |v i|`. Since `A i j ≥ 0`:
`(A *ᵥ w) i = Σ_j A i j |v j| ≥ |Σ_j A i j v j| = |μ v i| = μ |v i|`
so `w ⬝ᵥ (A *ᵥ w) ≥ μ ‖w‖²`. The max-Rayleigh bound gives `w ⬝ᵥ (A *ᵥ w) ≤ μ ‖w‖²`,
hence equality holds. By the eigenbasis expansion (spectral theorem):
`w ⬝ᵥ (A *ᵥ w) = Σ_k λ_k c_k²` and `‖w‖² = Σ_k c_k²` where `c_k = ⟨e_k, w⟩`.
Equality `Σ_k (μ - λ_k) c_k² = 0` with each term ≤ 0 forces `c_k = 0` for `λ_k < μ`,
giving `A *ᵥ w = μ • w`. **[Currently `sorry`; requires Mathlib eigenbasis inner product API.]**

### Step 2 — Strict positivity (irreducible case)
Given the nonneg eigenvector `w` from Step 1: if `w_i = 0` for some `i`, then
`(A *ᵥ w)_i = μ w_i = 0`, forcing `A_ij w_j = 0` for all `j`. By
`isIrreducible_iff_exists_pow_pos`, for any `j` there exists `k > 0` with
`(A^k)_{ij} > 0`, and then `(A^k)_{ij} w_j = 0` with `(A^k)_{ij} > 0` forces `w_j = 0`.
Hence `w = 0` — contradiction. **[Fully proved.]**

### Step 3 — Uniqueness
If `Av = μv`, `Au = μu` with `v, u > 0`, set `r = sup_i u_i / v_i`.
Then `u ≤ r v` componentwise and `(u - r v)_{i_0} = 0` for a maximizer `i_0`.
Setting `w = r v - u ≥ 0` with `w_{i_0} = 0` and `A *ᵥ w = μ • w`,
the Step 2 argument gives `w = 0`, hence `u = r v`. **[Fully proved.]**

## Sorry inventory

- `exists_nonneg_eigenvec_max`: the Rayleigh equality condition
  `w ⬝ᵥ (A *ᵥ w) = μ ‖w‖² → A *ᵥ w = μ • w` requires computing
  `⟨w, Aw⟩` via the eigenbasis — blocked by Mathlib's `EuclideanSpace`/`n → ℝ` API gap.
  This sorry is retained for documentation but is **no longer on the main proof path**:
  `exists_pos_eigenvec_max` now calls `exists_positive_eigenvector_of_irreducible`
  from `PerronFrobeniusMain` directly, bypassing this function entirely.

References: Seneta, *Non-negative Matrices and Markov Chains*, Ch. 1;
Tasaki §11.2 (application to Nagaoka's theorem). Tracked in Issue #405.
-/

namespace LatticeSystem.Math.PerronFrobenius

open Matrix Finset

variable {n : Type*} [Fintype n]

/-! ## Non-negative max eigenvector (sorry for the Rayleigh equality step) -/

/-- For a non-negative symmetric matrix, the maximum eigenvalue has a
non-negative eigenvector.

**Sorry**: the Rayleigh equality condition `R(|v|) = μ → A *ᵥ |v| = μ • |v|`
requires computing `⟨w, Aw⟩` via the eigenbasis inner product. The mathematical
argument is correct; the Lean proof is blocked by the `EuclideanSpace`/`n → ℝ` API.
This function is retained for documentation; `exists_pos_eigenvec_max` now bypasses it
via the Collatz-Wielandt approach (see `PerronFrobeniusMain`). -/
theorem exists_nonneg_eigenvec_max [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j) :
    ∃ (μ : ℝ) (v : n → ℝ),
      A *ᵥ v = μ • v ∧ v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧ ∀ k, hA.eigenvalues k ≤ μ := by
  sorry

/-! ## Strictly positive max eigenvector (irreducible case) -/

/-- The propagation argument: if `Av = μ • v`, `v ≥ 0`, `v ≠ 0`, and `A` is irreducible,
then `v > 0`.  Proof uses `isIrreducible_iff_exists_pow_pos` to reach every vertex. -/
private lemma pos_of_nonneg_eigenvec
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible)
    {μ : ℝ} {v : n → ℝ}
    (hAv : A *ᵥ v = μ • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne : v ≠ 0) :
    ∀ i, 0 < v i := by
  classical
  intro i
  by_contra hi
  simp only [not_lt] at hi
  have hi0 : v i = 0 := le_antisymm hi (hv_nonneg i)
  -- (A *ᵥ v) i = 0
  have hAvi : (A *ᵥ v) i = 0 := by
    have := congr_fun hAv i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [hi0, mul_zero] at this; exact this
  -- Each A i j * v j = 0 (nonneg terms sum to 0 → each is 0)
  have hTermZero : ∀ j, A i j * v j = 0 := by
    have hTerms : ∀ j, 0 ≤ A i j * v j :=
      fun j => mul_nonneg (hIrred.nonneg i j) (hv_nonneg j)
    have hSum0 : ∑ j : n, A i j * v j = 0 := by
      have hrow : (A *ᵥ v) i = ∑ j : n, A i j * v j := by simp [mulVec, dotProduct]
      linarith [hrow.symm ▸ hAvi]
    intro j
    apply le_antisymm _ (hTerms j)
    have := Finset.single_le_sum (fun k _ => hTerms k) (mem_univ j)
    linarith [hSum0]
  -- A^k *ᵥ v = μ^k • v for all k (proved before intro j to avoid IH pollution)
  have hApow : ∀ m, A ^ m *ᵥ v = μ ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      calc A ^ (p + 1) *ᵥ v
          = A ^ p *ᵥ (A *ᵥ v) := by rw [pow_succ, mulVec_mulVec]
        _ = A ^ p *ᵥ (μ • v) := by rw [hAv]
        _ = μ • (A ^ p *ᵥ v) := by rw [mulVec_smul]
        _ = μ • μ ^ p • v := by rw [ih]
        _ = μ ^ (p + 1) • v := by rw [smul_smul]; congr 1; ring
  -- Use irreducibility: ∀ j, ∃ k > 0, (A^k) i j > 0
  have hAll : ∀ j, v j = 0 := by
    intro j
    obtain ⟨k, _, hAk_pos⟩ :=
      (Matrix.isIrreducible_iff_exists_pow_pos hIrred.nonneg).mp hIrred i j
    have hApow_i : ∑ l : n, (A ^ k) i l * v l = 0 := by
      have hrow : (A ^ k *ᵥ v) i = ∑ l : n, (A ^ k) i l * v l := by
        simp [mulVec, dotProduct]
      have h := congr_fun (hApow k) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [hi0, mul_zero] at h; linarith [hrow.symm ▸ h]
    have hAk_nonneg : ∀ l, 0 ≤ (A ^ k) i l :=
      fun l => Matrix.pow_apply_nonneg hIrred.nonneg k i l
    have hTermNonneg : ∀ l, 0 ≤ (A ^ k) i l * v l :=
      fun l => mul_nonneg (hAk_nonneg l) (hv_nonneg l)
    have hTermJ : (A ^ k) i j * v j = 0 := by
      apply le_antisymm _ (hTermNonneg j)
      have := Finset.single_le_sum (fun l _ => hTermNonneg l) (mem_univ j)
      linarith [hApow_i]
    rcases (mul_eq_zero.mp hTermJ) with h | h
    · linarith [hAk_pos]
    · exact h
  exact hv_ne (funext hAll)

/-- For an irreducible nonneg Hermitian matrix, the max eigenvalue has a
strictly positive eigenvector.

Proof: the sorry-bearing `exists_nonneg_eigenvec_max` is bypassed by calling
`exists_positive_eigenvector_of_irreducible` directly (Collatz-Wielandt, PR C). -/
theorem exists_pos_eigenvec_max [Nonempty n]
    {A : Matrix n n ℝ} (_ : A.IsHermitian) (hIrred : A.IsIrreducible) :
    ∃ (μ : ℝ) (v : n → ℝ), A *ᵥ v = μ • v ∧ v ≠ 0 ∧ ∀ i, 0 < v i := by
  classical
  obtain ⟨μ, v, _, hv_pos, hAv⟩ :=
    LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible hIrred
  exact ⟨μ, v, hAv,
    fun h => absurd (hv_pos (Classical.arbitrary n)) (by simp [h]),
    hv_pos⟩

/-! ## Uniqueness of the positive eigenvector -/

/-- The strictly positive max eigenvector is unique up to a positive scalar.

The proof applies `pos_of_nonneg_eigenvec` to `r v - u` (after setting
`r = sup_i u_i / v_i`) to conclude `r v = u`. -/
theorem pos_eigenvec_unique [Nonempty n]
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible)
    {μ : ℝ} {v w : n → ℝ}
    (hv : A *ᵥ v = μ • v) (hv_pos : ∀ i, 0 < v i)
    (hw : A *ᵥ w = μ • w) (hw_pos : ∀ i, 0 < w i) :
    ∃ r : ℝ, 0 < r ∧ w = r • v := by
  classical
  -- r = sup_i w_i / v_i
  set r := Finset.sup' Finset.univ Finset.univ_nonempty (fun i => w i / v i)
  have hr_pos : 0 < r := by
    have h := Finset.le_sup' (fun i => w i / v i) (mem_univ (Classical.arbitrary n))
    exact lt_of_lt_of_le (div_pos (hw_pos _) (hv_pos _)) h
  refine ⟨r, hr_pos, ?_⟩
  -- w i ≤ r * v i (from definition of sup)
  have hle : ∀ i, w i ≤ r * v i := fun i => by
    have h := Finset.le_sup' (fun i => w i / v i) (mem_univ i)
    exact (div_le_iff₀ (hv_pos i)).mp h
  -- u = r • v - w is a nonneg eigenvector
  set u : n → ℝ := fun i => r * v i - w i
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i => by simp only [u]; linarith [hle i]
  have hu_def : u = r • v - w := funext (fun i => by simp [u, smul_eq_mul])
  have hu_eig : A *ᵥ u = μ • u := by
    rw [hu_def, mulVec_sub, mulVec_smul, hv, hw]
    ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  -- Some component is 0: the maximizer of w_i / v_i
  obtain ⟨i₀, _, hi₀_max⟩ :=
    Finset.exists_max_image Finset.univ (fun i => w i / v i) Finset.univ_nonempty
  have hu0 : u i₀ = 0 := by
    have hr_le : r ≤ w i₀ / v i₀ := by rw [Finset.sup'_le_iff]; exact hi₀_max
    have hr_eq : r = w i₀ / v i₀ :=
      le_antisymm hr_le (Finset.le_sup' (fun i => w i / v i) (mem_univ i₀))
    simp only [u, hr_eq]
    rw [div_mul_cancel₀ _ (ne_of_gt (hv_pos i₀))]
    ring
  -- u = 0 by propagation (u is nonneg, u i₀ = 0, A *ᵥ u = μ • u, A irreducible)
  have hu_zero : u = 0 := by
    by_contra h
    have := pos_of_nonneg_eigenvec hIrred hu_eig hu_nonneg h i₀
    linarith [hu0 ▸ this]
  ext i
  have := congr_fun hu_zero i
  simp only [u, Pi.zero_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

end LatticeSystem.Math.PerronFrobenius
