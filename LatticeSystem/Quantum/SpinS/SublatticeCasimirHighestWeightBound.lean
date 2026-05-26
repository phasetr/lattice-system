import LatticeSystem.Quantum.SpinS.SublatticeHighestWeight
import LatticeSystem.Quantum.SpinS.SublatticeMagSpectrum
import LatticeSystem.Quantum.SpinS.SublatticeSzBound

/-!
# Sublattice highest-weight Casimir bound

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

A non-zero highest-weight `(Ŝ_A)²`-eigenvector (annihilated by `Ŝ_A^+`) at a
sublattice magnetization `M` has Casimir eigenvalue `M(M+1)` (the sublattice
highest-weight relation, `SublatticeHighestWeight.lean`); since `M` must be an
attained basis eigenvalue (`SublatticeMagSpectrum.lean`), `|M| ≤ s_A`
(`SublatticeSzBound.lean`), so the Casimir eigenvalue is at most `s_A(s_A+1)`,
with `s_A = |A|·N/2`.

This is the sublattice analogue of `totalSpinSSquared_highestWeight_eigenvalue_re_le`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

omit [DecidableEq Λ] in
/-- The sublattice magnetization eigenvalue is real (imaginary part zero). -/
theorem sublatticeMagEigenvalueS_im_zero (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    (sublatticeMagEigenvalueS A σ).im = 0 := by
  rw [sublatticeMagEigenvalueS_def, Complex.im_sum]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  simp [Complex.sub_im]

/-- **Sublattice highest-weight Casimir bound**: a non-zero highest-weight
`(Ŝ_A)²`-eigenvector (`Ŝ_A^+ w = 0`) at `γ`, lying in `sublatticeMagSubspaceS A M`,
has `γ.re ≤ s_A(s_A+1)`, where `s_A = |A|·N/2`.  Its Casimir value is `M(M+1)`,
and `M` is an attained basis eigenvalue, so `|M| ≤ s_A`. -/
theorem sublatticeSpinSquaredS_highestWeight_eigenvalue_re_le
    (A : Λ → Bool) {γ M : ℂ} {w : (Λ → Fin (N + 1)) → ℂ}
    (hw_ne : w ≠ 0)
    (hw_mem : w ∈ sublatticeMagSubspaceS A M)
    (hker : (sublatticeSpinSOpPlus N A).mulVec w = 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec w = γ • w) :
    γ.re ≤
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2) + 1) := by
  set sA : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2
    with hsA
  -- γ = M (M + 1).
  rw [mem_sublatticeMagSubspaceS_iff] at hw_mem
  have hhw := sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpPlus_eq_zero A hw_mem hker
  have hsmul : γ • w = (M * (M + 1)) • w := hcas.symm.trans hhw
  have hγ : γ = M * (M + 1) := by
    have := sub_eq_zero.mpr hsmul
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw_ne
  -- M is an attained basis eigenvalue.
  have hMspec : ∃ σ : Λ → Fin (N + 1), sublatticeMagEigenvalueS A σ = M := by
    by_contra h
    exact hw_ne ((Submodule.eq_bot_iff _).mp
      (sublatticeMagSubspaceS_eq_bot_of_not_in_spectrum A (not_exists.mp h)) w hw_mem)
  obtain ⟨σ, hσ⟩ := hMspec
  -- Bounds |M.re| ≤ s_A, M.im = 0.
  subst hγ
  have hMre_abs : |M.re| ≤ sA := by
    rw [← hσ, hsA]
    exact sublatticeSpinSOp3_eigenvalue_re_abs_le_sA A σ
  rw [abs_le] at hMre_abs
  have hMim : M.im = 0 := by rw [← hσ]; exact sublatticeMagEigenvalueS_im_zero A σ
  -- (M*(M+1)).re = M.re*(M.re+1) since M.im = 0.
  have hre : (M * (M + 1)).re = M.re * (M.re + 1) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, hMim]
    ring
  rw [hre]
  have hsA_nn : (0 : ℝ) ≤ sA := by rw [hsA]; positivity
  nlinarith [hMre_abs.1, hMre_abs.2, hsA_nn]

end LatticeSystem.Quantum
