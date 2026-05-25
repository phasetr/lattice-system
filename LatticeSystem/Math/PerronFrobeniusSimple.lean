import LatticeSystem.Math.PerronFrobenius

/-!
# Perron–Frobenius: geometric simplicity of the Perron eigenvalue

For an irreducible non-negative matrix with a strictly positive eigenvector
`v` at eigenvalue `μ`, every (real) eigenvector at the same eigenvalue is a
scalar multiple of `v`; i.e. the `μ`-eigenspace is one-dimensional.

This strengthens `pos_eigenvec_unique` (uniqueness among *strictly positive*
eigenvectors) to *all* eigenvectors, via the standard perturbation trick: for
a small `t > 0` the vector `v + t • u` is still strictly positive and is an
eigenvector at `μ`, hence proportional to `v` by `pos_eigenvec_unique`, which
forces `u` to be proportional to `v`.

This is the simplicity needed to conclude that a Perron ground state is a
joint eigenvector of any commuting operator (e.g. the total Casimir), used in
the Tasaki §2.5 Theorem 2.3 total-spin determination.
-/

namespace LatticeSystem.Math.PerronFrobenius

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Geometric simplicity of the Perron eigenvalue**: if `A` is irreducible,
`v` is a strictly positive eigenvector at `μ`, and `u` is any real eigenvector
at the same `μ`, then `u = s • v` for some real scalar `s`. -/
theorem eigenvec_proportional_of_pos_eigenvec [Nonempty n]
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible)
    {μ : ℝ} {v u : n → ℝ}
    (hv : A *ᵥ v = μ • v) (hv_pos : ∀ i, 0 < v i)
    (hu : A *ᵥ u = μ • u) :
    ∃ s : ℝ, u = s • v := by
  classical
  -- A small positive `t` so that `v + t • u` is still strictly positive.
  set t : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty (fun i => v i / (|u i| + 1)) with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def, Finset.lt_inf'_iff]
    intro i _
    have h1 : (0 : ℝ) < |u i| + 1 := by positivity
    exact div_pos (hv_pos i) h1
  have ht_le : ∀ i, t ≤ v i / (|u i| + 1) := by
    intro i
    rw [ht_def]
    exact Finset.inf'_le (fun i => v i / (|u i| + 1)) (Finset.mem_univ i)
  -- Hence `t * |u i| < v i` for every `i`.
  have ht_bound : ∀ i, t * |u i| < v i := by
    intro i
    have h1 : (0 : ℝ) < |u i| + 1 := by positivity
    have h2 : t * (|u i| + 1) ≤ v i := (le_div_iff₀ h1).mp (ht_le i)
    have h3 : t * |u i| < t * (|u i| + 1) :=
      mul_lt_mul_of_pos_left (by linarith) ht_pos
    linarith
  -- `w := v + t • u` is strictly positive and an eigenvector at `μ`.
  set w : n → ℝ := v + t • u with hw_def
  have hw_pos : ∀ i, 0 < w i := by
    intro i
    have hb := ht_bound i
    have : -(t * |u i|) ≤ t * u i := by
      have := neg_abs_le (u i)
      nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le (u i)) (le_of_lt ht_pos)]
    simp only [hw_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [ht_bound i, neg_abs_le (u i),
      mul_le_mul_of_nonneg_left (neg_abs_le (u i)) (le_of_lt ht_pos)]
  have hw_eig : A *ᵥ w = μ • w := by
    rw [hw_def, Matrix.mulVec_add, hv, Matrix.mulVec_smul, hu, smul_add, smul_smul,
      smul_smul, mul_comm]
  -- Uniqueness among positive eigenvectors: `w = r • v` for some `r > 0`.
  obtain ⟨r, _hr_pos, hwr⟩ := pos_eigenvec_unique hIrred hv hv_pos hw_eig hw_pos
  -- `v + t • u = r • v` ⟹ `t • u = (r - 1) • v` ⟹ `u = ((r-1)/t) • v`.
  refine ⟨(r - 1) / t, ?_⟩
  have heq : t • u = (r - 1) • v := by
    have : v + t • u = r • v := by rw [← hw_def]; exact hwr
    funext i
    have := congrFun this i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  funext i
  have hi := congrFun heq i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  field_simp
  linarith [hi]

end LatticeSystem.Math.PerronFrobenius
