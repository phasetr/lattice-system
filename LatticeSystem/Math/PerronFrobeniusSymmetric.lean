import LatticeSystem.Math.PerronFrobeniusMain
import LatticeSystem.Math.PerronFrobeniusFinrank

/-!
# Tasaki Appendix A.4.1: Perron–Frobenius for a real symmetric matrix (Theorem A.18)

Tasaki's Theorem A.18, "the key" tool behind many ground-state uniqueness arguments in the book
(§2.4, §5.1, §11.2, §11.5): a real *symmetric* matrix `M` whose off-diagonal entries are
nonpositive (`M_{ij} ≤ 0` for `i ≠ j`) and whose nonzero off-diagonal entries connect all indices
(irreducibility) has a **nondegenerate lowest eigenvalue**, whose eigenvector can be taken with all
strictly positive components.

We package the hypotheses (i)+(ii) of Tasaki as the irreducibility of the shifted matrix
`Â = c·1 − M` (`Matrix.IsIrreducible`, i.e. entrywise nonnegative with a strongly connected support
quiver) — exactly the form the concrete models in this repository already establish, and which for
suitable `c` is equivalent to Tasaki's (i) `M_{ij} ≤ 0` and (ii) connectivity.  The proof reuses the
project's Collatz–Wielandt Perron–Frobenius (`exists_positive_eigenvector_of_irreducible`) for the
positive eigenvector and the eigenspace simplicity (`eigenspace_finrank_le_one_of_pos_eigenvec`) for
the nondegeneracy; the only genuinely new ingredient is the variational `|w|`-argument (Tasaki's
eq. (A.4.1)) showing the eigenvalue with the positive eigenvector is the *lowest* one.  All proved
(axiom-free).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.4.1, Theorem A.18, eq. (A.4.1), pp. 475–476.
-/

namespace LatticeSystem.Math

open Matrix Finset Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Tasaki Theorem A.18 (Perron–Frobenius for a real symmetric matrix).**  Let `M` be a real
symmetric matrix such that the shifted matrix `Â = c·1 − M` is irreducible (entrywise nonnegative
with strongly connected support — Tasaki's `M_{ij} ≤ 0` off-diagonal plus connectivity).  Then there
is an eigenvalue `μ` of `M` with a strictly positive eigenvector `v` (`v_i > 0`, `M v = μ v`); `μ`
is the *lowest* eigenvalue (`μ ≤ λ` for every eigenvalue `λ`); and it is *nondegenerate* (its
eigenspace is at most one-dimensional). -/
theorem perronFrobenius_real_symmetric (M : Matrix n n ℝ) (hsymm : M.IsSymm) (c : ℝ)
    (hc : (c • (1 : Matrix n n ℝ) - M).IsIrreducible) :
    ∃ (μ : ℝ) (v : n → ℝ), (∀ i, 0 < v i) ∧ M *ᵥ v = μ • v ∧
      (∀ (lam : ℝ) (w : n → ℝ), w ≠ 0 → M *ᵥ w = lam • w → μ ≤ lam) ∧
      finrank ℝ (End.eigenspace (Matrix.toLin' M) μ) ≤ 1 := by
  classical
  set A : Matrix n n ℝ := c • (1 : Matrix n n ℝ) - M with hA
  have hMA : M = c • (1 : Matrix n n ℝ) - A := by rw [hA]; abel
  have hAsymm : Aᵀ = A := by
    rw [hA, transpose_sub, transpose_smul, transpose_one, hsymm.eq]
  -- Positive eigenvector of the irreducible nonnegative `A` at a positive eigenvalue `r`.
  obtain ⟨r, v, _, hv_pos, hAv⟩ :=
    PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible hc
  set μ : ℝ := c - r with hμ
  -- `M v = (c − r) v = μ v`.
  have hMv : M *ᵥ v = μ • v := by
    rw [hMA, sub_mulVec, smul_mulVec, one_mulVec, hAv, hμ, sub_smul]
  refine ⟨μ, v, hv_pos, hMv, ?_, ?_⟩
  · -- Lowest eigenvalue: the variational `|w|`-argument (eq. (A.4.1)).
    intro lam w hw hMw
    have hAw : A *ᵥ w = (c - lam) • w := by
      rw [hA, sub_mulVec, smul_mulVec, one_mulVec, hMw, sub_smul]
    set ρ : ℝ := c - lam with hρ
    set aw : n → ℝ := fun i => |w i| with haw
    have hnn : ∀ i j, 0 ≤ A i j := hc.nonneg
    -- Each component: `ρ · |w_i| ≤ (A |w|)_i`.
    have hclaim : ∀ i, ρ * aw i ≤ (A *ᵥ aw) i := by
      intro i
      have htri : |(A *ᵥ w) i| ≤ (A *ᵥ aw) i := by
        rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
        calc |∑ j, A i j * w j| ≤ ∑ j, |A i j * w j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, A i j * aw j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [abs_mul, abs_of_nonneg (hnn i j), haw]
      have hval : (A *ᵥ w) i = ρ * w i := by
        rw [hAw]; simp [Pi.smul_apply, smul_eq_mul]
      have hle1 : ρ * aw i ≤ |(A *ᵥ w) i| := by
        rw [hval, abs_mul, haw]
        exact mul_le_mul_of_nonneg_right (le_abs_self ρ) (abs_nonneg (w i))
      linarith [htri, hle1]
    -- Pair against the positive eigenvector: `r · (v · |w|) = v · (A |w|) ≥ ρ · (v · |w|)`.
    have hquad : v ⬝ᵥ (A *ᵥ aw) = r * (v ⬝ᵥ aw) := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hAsymm, hAv, smul_dotProduct,
        smul_eq_mul]
    have hsum : ρ * (v ⬝ᵥ aw) ≤ r * (v ⬝ᵥ aw) := by
      rw [← hquad, dotProduct, dotProduct, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hclaim i
      have hvi := (hv_pos i).le
      calc ρ * (v i * aw i) = v i * (ρ * aw i) := by ring
        _ ≤ v i * (A *ᵥ aw) i := mul_le_mul_of_nonneg_left this hvi
    have hvaw_pos : 0 < v ⬝ᵥ aw := by
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hw
      refine Finset.sum_pos' (fun i _ => mul_nonneg (hv_pos i).le (abs_nonneg _))
        ⟨i₀, mem_univ _, ?_⟩
      exact mul_pos (hv_pos i₀) (abs_pos.mpr hi₀)
    have hρr : ρ ≤ r := le_of_mul_le_mul_right hsum hvaw_pos
    rw [hμ]; linarith
  · -- Nondegeneracy: the `M`-eigenspace at `μ` equals the `A`-eigenspace at `r`, which is ≤ 1-dim.
    have heq : End.eigenspace (Matrix.toLin' M) μ = End.eigenspace (Matrix.toLin' A) r := by
      ext w
      rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.toLin'_apply,
        hMA, sub_mulVec, smul_mulVec, one_mulVec, hμ, sub_smul]
      constructor <;> intro h
      · exact sub_right_inj.mp h
      · rw [h]
    rw [heq]
    exact PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec hc hAv hv_pos

end LatticeSystem.Math
