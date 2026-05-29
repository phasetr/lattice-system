import LatticeSystem.Math.HermitianMaxEigenvalue
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectrum shift identity for Hermitian min/max eigenvalues

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.g): For a Hermitian matrix `M : Matrix n n ℂ` and a real scalar `c`,
the shifted matrix `B := c • 1 - M` is also Hermitian, and
`hermitianMinEigenvalue M = c - hermitianMaxEigenvalue B`.

**Proof.** From `spectrum.singleton_sub_eq`:
```
spectrum ℝ B = {c} - spectrum ℝ M
range eigenvalues_B = c - range eigenvalues_M
```
So:
```
hermitianMaxEigenvalue B = max(c - eigenvalues_M)
                         = c - min(eigenvalues_M)
                         = c - hermitianMinEigenvalue M.
```

This identity is the final spectral bridge for (j.13) — combined with
(j.13.f) `hermitianMaxEigenvalue B_complex = μ_PF`, it gives
`hermitianMinEigenvalue M_complex = c - μ_PF = ν_PF`, discharging the
(j.11)/(j.12) capstone hypothesis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Fintype n] [Nonempty n] in
/-- **Hermitian property is preserved by `c • 1 - ·`** for real `c`. -/
theorem isHermitian_smul_one_sub_of_real
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • (1 : Matrix n n ℂ) - M).IsHermitian := by
  have h1 : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
    (Matrix.isHermitian_one.smul (Complex.conj_ofReal c))
  exact h1.sub hM

/-- **Spectrum shift identity for Hermitian min/max eigenvalues**: for Hermitian
`M : Matrix n n ℂ` and real `c`,
`hermitianMinEigenvalue M = c - hermitianMaxEigenvalue (c • 1 - M)`. -/
theorem hermitianMinEigenvalue_eq_sub_hermitianMaxEigenvalue_shift
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    LatticeSystem.Quantum.hermitianMinEigenvalue hM =
      c - hermitianMaxEigenvalue (isHermitian_smul_one_sub_of_real hM c) := by
  set B := (c : ℂ) • (1 : Matrix n n ℂ) - M with hB_def
  set hB := isHermitian_smul_one_sub_of_real hM c
  -- Strategy: relate the image of eigenvalues_B to (c - ·) of image of eigenvalues_M.
  -- range eigenvalues_B = spectrum ℝ B = {c} - spectrum ℝ M = c - range eigenvalues_M.
  -- Hence (Finset image B-eigenvalues) = (Finset image M-eigenvalues).image (c - ·).
  -- max' of LHS = c - min' of RHS (antitone of c - ·).
  have h_alg_eq : (algebraMap ℝ (Matrix n n ℂ)) c - M = B := by
    rw [Algebra.algebraMap_eq_smul_one (R := ℝ) (A := Matrix n n ℂ) c]
    rfl
  have h_imageB_eq :
      ((Finset.univ : Finset n).image hB.eigenvalues) =
        ((Finset.univ : Finset n).image hM.eigenvalues).image (fun lam => c - lam) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx_mem
      rw [Finset.mem_image] at hx_mem
      obtain ⟨i, _, hi⟩ := hx_mem
      have h_x_in_spec : x ∈ spectrum ℝ B := by
        rw [hB.spectrum_real_eq_range_eigenvalues]; exact ⟨i, hi⟩
      rw [← h_alg_eq, ← spectrum.singleton_sub_eq] at h_x_in_spec
      obtain ⟨a, ha_mem, b, hb_mem, hxab⟩ := h_x_in_spec
      rw [Set.mem_singleton_iff] at ha_mem
      rw [hM.spectrum_real_eq_range_eigenvalues] at hb_mem
      obtain ⟨j, hj⟩ := hb_mem
      rw [Finset.mem_image]
      refine ⟨hM.eigenvalues j, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      · simp only at hxab
        rw [ha_mem, ← hj] at hxab
        linarith
    · intro hx_mem
      rw [Finset.mem_image] at hx_mem
      obtain ⟨y, hy_mem, hxy⟩ := hx_mem
      rw [Finset.mem_image] at hy_mem
      obtain ⟨j, _, hj⟩ := hy_mem
      -- x = c - y, y = hM.eigenvalues j.
      have h_mu_spec : hM.eigenvalues j ∈ spectrum ℝ M := by
        rw [hM.spectrum_real_eq_range_eigenvalues]; exact ⟨j, rfl⟩
      have h_x_spec : x ∈ spectrum ℝ B := by
        rw [← h_alg_eq, ← spectrum.singleton_sub_eq]
        refine ⟨c, Set.mem_singleton c, hM.eigenvalues j, h_mu_spec, ?_⟩
        rw [← hj] at hxy; linarith
      rw [hB.spectrum_real_eq_range_eigenvalues] at h_x_spec
      obtain ⟨i, hi⟩ := h_x_spec
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  -- Now we have: image B-eigenvalues = (image M-eigenvalues).image (c - ·).
  -- max' (image B-eigenvalues) = c - min' (image M-eigenvalues).
  set S := (Finset.univ : Finset n).image hM.eigenvalues with hS_def
  set Sc := S.image (fun lam => c - lam) with hSc_def
  have hS_ne : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  have hSc_ne : Sc.Nonempty := Finset.image_nonempty.mpr hS_ne
  -- Key arithmetic: max' Sc = c - min' S.
  have h_max_eq : Sc.max' hSc_ne = c - S.min' hS_ne := by
    apply le_antisymm
    · apply Finset.max'_le
      intro z hz
      obtain ⟨w, hw_mem, hwz⟩ := Finset.mem_image.mp hz
      have hmw : S.min' hS_ne ≤ w := S.min'_le w hw_mem
      linarith
    · have hmem : c - S.min' hS_ne ∈ Sc :=
        Finset.mem_image.mpr ⟨S.min' hS_ne, S.min'_mem hS_ne, rfl⟩
      exact Finset.le_max' _ _ hmem
  -- Conclude. hermitianMaxEigenvalue hB equals max' over Finset.image hB.eigenvalues,
  -- which equals max' Sc via h_imageB_eq.
  -- hermitianMinEigenvalue hM = min' S, and c - max' Sc = c - (c - min' S) = min' S.
  have h_max_B : hermitianMaxEigenvalue hB = Sc.max' hSc_ne := by
    unfold hermitianMaxEigenvalue
    congr 1
  have h_min_M : LatticeSystem.Quantum.hermitianMinEigenvalue hM = S.min' hS_ne := rfl
  rw [h_min_M, h_max_B, h_max_eq]
  ring

end LatticeSystem.Math
