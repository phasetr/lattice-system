import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# Rayleigh quotient on a diagonal matrix

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

For a diagonal matrix `Matrix.diagonal f : Matrix n n ℂ` and a vector
`v : n → ℂ`, the Rayleigh quotient is the eigenvalue-weighted sum of squares
`Σ_i ‖v_i‖² · (f i).re` (when `f i` is real for each `i`).

This is the key explicit computation underlying the variational principle:
for Hermitian `M = U D U†` with `D = Matrix.diagonal (eigenvalues)`, the
Rayleigh quotient transforms under unitary similarity to a sum of weighted
eigenvalues. Combined with the unit-norm invariance, this yields
`rayleighOnVec M v ≥ min eigenvalue` for unit `v` — the variational lower
bound needed by the obligation (2) deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `rayleighOnVec (diagonal f) v = Σ_i ‖v_i‖² · (f i).re` when each `f i` is real. -/
theorem rayleighOnVec_diagonal_of_real (f : n → ℂ)
    (_hf : ∀ i, (f i).im = 0) (v : n → ℂ) :
    rayleighOnVec (Matrix.diagonal f) v = ∑ i, ‖v i‖ ^ 2 * (f i).re := by
  unfold rayleighOnVec
  have hpw : Matrix.diagonal f *ᵥ v = fun i => f i * v i := by
    funext i; exact Matrix.mulVec_diagonal f v i
  rw [hpw]
  -- dotProduct (star v) (fun i => f i * v i) = Σ_i conj(v_i) * (f i * v_i)
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [show (∑ i, (starRingEnd ℂ) (v i) * (f i * v i)).re =
        ∑ i, ((starRingEnd ℂ) (v i) * (f i * v i)).re from Complex.re_sum _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- conj(v_i) * (f_i * v_i) = f_i * (conj(v_i) * v_i) = f_i * ‖v_i‖²
  rw [show (starRingEnd ℂ) (v i) * (f i * v i) = f i * ((starRingEnd ℂ) (v i) * v i) from by
        ring]
  rw [show ((starRingEnd ℂ) (v i) * v i : ℂ) = ((‖v i‖ ^ 2 : ℝ) : ℂ) from by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  ring

/-- Specialisation to a real-valued eigenvalue array (as arises from
`Matrix.IsHermitian.eigenvalues`): `rayleighOnVec (diagonal (↑lam : n → ℂ)) v
= Σ ‖v_i‖² · lam i`. -/
theorem rayleighOnVec_diagonal_real (lam : n → ℝ) (v : n → ℂ) :
    rayleighOnVec (Matrix.diagonal (fun i => (lam i : ℂ))) v =
      ∑ i, ‖v i‖ ^ 2 * lam i := by
  rw [rayleighOnVec_diagonal_of_real _ (fun _ => rfl) v]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re]

end LatticeSystem.Quantum
