import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag
import LatticeSystem.Quantum.SpinS.SingleIonOffDiag

/-!
# Real entries of the axis-swapped anisotropic Heisenberg Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f.3-finish) step 1: under real coefficients (`(J x y).im = 0`, `lam.im = 0`, `D.im = 0`),
every entry of `axisSwappedAnisotropicHeisenbergS J lam D N` has imaginary part zero.

This is one of the foundational lemmas needed to bridge the real-form parity-block matrix
`finrank ≤ 1` (#3827) to the complex parity-block matrix `finrank ≤ 1` via the real-to-complex
eigenspace bridge (#3828): the matrix identity
`(dressed_re.submatrix valS valS).map ((↑) : ℝ → ℂ) = dressed_complex.submatrix valS valS`
needs every entry of `dressed_complex` (and hence of `axisSwapped`) to be real.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Single-ion `(Ŝ²)²` entry has imaginary part zero (off the on-site change)**: for any
`(σ, τ)`, the on-site `(Ŝ²)²` matrix entry has `im = 0` (vanishes if `σ, τ` don't agree off `x`,
or is the off-diagonal of `spinSOp2²` at `(σ x, τ x)` otherwise — both have `im = 0`). -/
theorem onSiteS_spinSOp2_sq_apply_im_zero
    (x : Λ) (σ τ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ τ).im = 0 := by
  rw [onSiteS_apply]
  by_cases hagree : ∀ k, k ≠ x → σ k = τ k
  · rw [if_pos hagree]
    by_cases hx : σ x = τ x
    · -- Diagonal of spinSOp2², via Hermitian + diag = real.
      rw [hx]
      have hH : (spinSOp2 N * spinSOp2 N).IsHermitian :=
        (Matrix.IsHermitian.mul_of_commute (spinSOp2_isHermitian N)
          (spinSOp2_isHermitian N) rfl)
      have := hH.apply (τ x) (τ x)
      -- this : star ((spinSOp2 N * spinSOp2 N) (τ x) (τ x)) = (spinSOp2 N * spinSOp2 N) (τ x) (τ x)
      rw [Complex.star_def, Complex.conj_eq_iff_im] at this
      exact this
    · exact spinSOp2_mul_spinSOp2_apply_offdiag_im_zero N hx
  · rw [if_neg hagree]
    simp

/-- **Axis-swapped `Ĥ'` entries are real under real coefficients**. -/
theorem axisSwappedAnisotropicHeisenbergS_apply_im_zero
    {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0) (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0)
    (σ τ : Λ → Fin (N + 1)) :
    (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N σ τ).im = 0 := by
  by_cases hστ : σ = τ
  · -- Diagonal: use Hermitian + conj = self → im = 0.
    subst hστ
    have hH := axisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
      (J := J) (lam := lam) (D := D)
      (fun x y => by
        rw [Complex.star_def, Complex.conj_eq_iff_im]
        exact hJim x y)
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hDim)
    have hi := hH.apply σ σ
    rw [Complex.star_def, Complex.conj_eq_iff_im] at hi
    exact hi
  · -- Off-diagonal: bond + single-ion, each has im = 0.
    rw [axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, Complex.add_im]
    have hbond : ((∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N :
        Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ) σ τ).im = 0 := by
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.im_sum]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      refine Finset.sum_eq_zero (fun y _ => ?_)
      by_cases hxy : x = y
      · subst hxy; rw [hJself x]; simp
      · rw [Complex.mul_im, hJim x y, zero_mul, add_zero,
            spinSDotXXZSwap_apply_im_zero hxy hlam hστ, mul_zero]
    have hsi : (singleIonAnisotropyS2 (Λ := Λ) D N σ τ).im = 0 := by
      unfold singleIonAnisotropyS2
      rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_im, hDim, zero_mul, add_zero,
          Matrix.sum_apply, Complex.im_sum]
      have hsum : ∑ x : Λ, ((onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N) :
          ManyBodyOpS Λ N) σ τ).im = 0 := by
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [onSiteS_sq]
        exact onSiteS_spinSOp2_sq_apply_im_zero x σ τ
      rw [hsum]; ring
    rw [hbond, hsi]; ring

end LatticeSystem.Quantum
