import LatticeSystem.Math.PerronFrobeniusMain
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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
giving `A *ᵥ w = μ • w`.

### Step 2 — Strict positivity (irreducible case)
Given the nonneg eigenvector `w` from Step 1: if `w_i = 0` for some `i`, then
`(A *ᵥ w)_i = μ w_i = 0`, forcing `A_ij w_j = 0` for all `j`. By
`isIrreducible_iff_exists_pow_pos`, for any `j` there exists `k > 0` with
`(A^k)_{ij} > 0`, and then `(A^k)_{ij} w_j = 0` with `(A^k)_{ij} > 0` forces `w_j = 0`.
Hence `w = 0` — contradiction.

### Step 3 — Uniqueness
If `Av = μv`, `Au = μu` with `v, u > 0`, set `r = sup_i u_i / v_i`.
Then `u ≤ r v` componentwise and `(u - r v)_{i_0} = 0` for a maximizer `i_0`.
Setting `w = r v - u ≥ 0` with `w_{i_0} = 0` and `A *ᵥ w = μ • w`,
the Step 2 argument gives `w = 0`, hence `u = r v`.

Step 1 is stated here for orientation only; the main proof path does not go
through it.  `exists_pos_eigenvec_max` obtains the strictly positive eigenvector
from `exists_positive_eigenvector_of_irreducible` (`PerronFrobeniusMain`), which
follows the Collatz–Wielandt route instead.

References: Seneta, *Non-negative Matrices and Markov Chains*, Ch. 1;
Tasaki §11.2 (application to Nagaoka's theorem).
-/

namespace LatticeSystem.Math.PerronFrobenius

open Matrix Finset

variable {n : Type*} [Fintype n]

/-! ## Strictly positive max eigenvector (irreducible case) -/

/-- For an irreducible nonneg Hermitian matrix, the max eigenvalue has a
strictly positive eigenvector.

Proof: `exists_positive_eigenvector_of_irreducible` is called directly
(Collatz–Wielandt, PR C). -/
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
    have := LatticeSystem.Math.PerronFrobeniusMain.pos_of_nonneg_eigenvec
      hIrred hu_eig hu_nonneg h i₀
    linarith [hu0 ▸ this]
  ext i
  have := congr_fun hu_zero i
  simp only [u, Pi.zero_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

end LatticeSystem.Math.PerronFrobenius
