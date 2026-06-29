import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHermitianAbs
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionTrace
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSRPRearrangement

/-!
# The abstract spin-reflection-positivity interaction inequality (Tasaki §10.2.4)

Thirty-first layer (PR31) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

The interaction part of Lieb's energy inequality `E(W) ≥ E(|W|)` is the matrix
inequality, for Hermitian `W` and Hermitian `I`,

  `Re tr(W·I·W·I) ≤ Re tr(|W|·I·|W|·I)`.

Diagonalizing `W = U·D·Uᴴ` (spectral theorem) and setting `M = Uᴴ·I·U` (Hermitian),
the trace expands to the spectral double sum
`Re tr(W·I·W·I) = Σ_{j,k} λ_j λ_k |M_{j,k}|²`; the same expansion for `|W| = U·|D|·Uᴴ`
gives `Σ_{j,k} |λ_j| |λ_k| |M_{j,k}|²`, and the elementary rearrangement
`lieb_srp_rearrangement` (PR29) closes the inequality (the weights `|M_{j,k}|² ≥ 0`).

## Main results

* `trace_conj_diag_interaction_re_eq_spectral_sum` — the spectral double-sum form of
  `Re tr((U·diag g·Uᴴ)·I·(U·diag g·Uᴴ)·I)`.
* `trace_hermitian_interaction_re_le_abs` — the interaction inequality
  `Re tr(W·I·W·I) ≤ Re tr(|W|·I·|W|·I)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.41)–(10.2.43); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral double-sum form of the conjugated diagonal interaction trace. For a
unitary `U`, Hermitian `I`, and real weights `g`, with `M = Uᴴ·I·U`,
`tr((U·diag g·Uᴴ)·I·(U·diag g·Uᴴ)·I) = Σ_{j,k} g_j g_k |M_{j,k}|²`. -/
theorem trace_conj_diag_interaction_eq_spectral_sum (U I : Matrix n n ℂ)
    (hI : I.IsHermitian) (g : n → ℝ) :
    Matrix.trace ((U * Matrix.diagonal (RCLike.ofReal ∘ g) * Uᴴ) * I *
        (U * Matrix.diagonal (RCLike.ofReal ∘ g) * Uᴴ) * I)
      = ∑ j : n, ∑ k : n, (RCLike.ofReal (g j) * RCLike.ofReal (g k)) *
          (Complex.normSq ((Uᴴ * I * U) j k) : ℂ) := by
  have hMherm : (Uᴴ * I * U).IsHermitian := isHermitian_conjTranspose_mul_mul U hI
  set Dg : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ g) with hDg
  -- Rotate the leading `U` to the back, regroup `Uᴴ·I·U` as `M`; then one more cyclic.
  have e1 : Matrix.trace ((U * Dg * Uᴴ) * I * (U * Dg * Uᴴ) * I)
      = Matrix.trace (Dg * (Uᴴ * I * U) * Dg * (Uᴴ * I * U)) := by
    rw [show (U * Dg * Uᴴ) * I * (U * Dg * Uᴴ) * I
          = U * (Dg * Uᴴ * I * U * Dg * Uᴴ * I) from by noncomm_ring, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have e2 : Matrix.trace (Dg * (Uᴴ * I * U) * Dg * (Uᴴ * I * U))
      = Matrix.trace ((Uᴴ * I * U)ᴴ * (Dg * (Uᴴ * I * U) * Dg)) := by
    rw [hMherm.eq, Matrix.trace_mul_comm]
  rw [e1, e2, hDg, trace_conjTranspose_mul_diagonal_mul_diagonal_eq_sum_normSq]
  simp only [Function.comp_apply]

omit [DecidableEq n] in
/-- The real part of the spectral double-sum is the real double-sum. -/
private theorem re_spectral_sum (M : Matrix n n ℂ) (g : n → ℝ) :
    (∑ j : n, ∑ k : n, (RCLike.ofReal (g j) * RCLike.ofReal (g k)) *
        (Complex.normSq (M j k) : ℂ)).re
      = ∑ j : n, ∑ k : n, g j * g k * Complex.normSq (M j k) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change (((g j : ℝ) : ℂ) * ((g k : ℝ) : ℂ) * (Complex.normSq (M j k) : ℂ)).re
    = g j * g k * Complex.normSq (M j k)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real part of the conjugated diagonal interaction trace as the real
spectral double-sum. -/
theorem trace_conj_diag_interaction_re_eq_spectral_sum (U I : Matrix n n ℂ)
    (hI : I.IsHermitian) (g : n → ℝ) :
    (Matrix.trace ((U * Matrix.diagonal (RCLike.ofReal ∘ g) * Uᴴ) * I *
        (U * Matrix.diagonal (RCLike.ofReal ∘ g) * Uᴴ) * I)).re
      = ∑ j : n, ∑ k : n, g j * g k * Complex.normSq ((Uᴴ * I * U) j k) := by
  rw [trace_conj_diag_interaction_eq_spectral_sum U I hI g, re_spectral_sum]

/-- **The abstract SRP interaction inequality.** For Hermitian `W` and Hermitian `I`,
`Re tr(W·I·W·I) ≤ Re tr(|W|·I·|W|·I)`. -/
theorem trace_hermitian_interaction_re_le_abs {W : Matrix n n ℂ} (hW : W.IsHermitian)
    {I : Matrix n n ℂ} (hI : I.IsHermitian) :
    (Matrix.trace (W * I * W * I)).re
      ≤ (Matrix.trace (hermitianAbs hW * I * hermitianAbs hW * I)).re := by
  set U := (hW.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hWspec : W = U * Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) * Uᴴ := by
    conv_lhs => rw [hW.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hU]
  have hAbsspec : hermitianAbs hW
      = U * Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) * Uᴴ := by
    rw [hermitianAbs, ← hU]
  have hL : (Matrix.trace (W * I * W * I)).re
      = ∑ j : n, ∑ k : n, hW.eigenvalues j * hW.eigenvalues k *
          Complex.normSq ((Uᴴ * I * U) j k) := by
    conv_lhs => rw [hWspec]
    exact trace_conj_diag_interaction_re_eq_spectral_sum U I hI hW.eigenvalues
  have hR : (Matrix.trace (hermitianAbs hW * I * hermitianAbs hW * I)).re
      = ∑ j : n, ∑ k : n, |hW.eigenvalues j| * |hW.eigenvalues k| *
          Complex.normSq ((Uᴴ * I * U) j k) := by
    conv_lhs => rw [hAbsspec]
    exact trace_conj_diag_interaction_re_eq_spectral_sum U I hI (fun i => |hW.eigenvalues i|)
  rw [hL, hR]
  exact lieb_srp_rearrangement hW.eigenvalues
    (fun j k => Complex.normSq ((Uᴴ * I * U) j k))
    (fun j k => Complex.normSq_nonneg _)

end LatticeSystem.Fermion
