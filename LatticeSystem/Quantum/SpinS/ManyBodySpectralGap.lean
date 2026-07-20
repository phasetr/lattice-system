/-
Model-independent spectral infrastructure for many-body chain operators.

Everything here is stated for an arbitrary chain operator `H : ManyBodyOpS (Fin L) N`; no model,
no spin value and no chain length is fixed.  The eigenvalue ↔ `realSpectrum` bridge and the
first-excited-eigenvalue constructor are the shared core of the spectral-gap arguments of the
library; they are consumed here by the Lieb–Schultz–Mattis ring gap (Tasaki §6.2 Theorem 6.3,
`LiebSchultzMattisRingGap.lean`).
-/
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Generic spectral lemmas for many-body chain operators

For a Hermitian chain operator `H : ManyBodyOpS (Fin L) N` this module relates the Hermitian
eigenvalue family `hH.eigenvalues` to the `realSpectrum` of `H`
(`Quantum/SpinS/HaldaneConjecture.lean`) and constructs the first excited eigenvalue.

* `eigenvalues_mem_realSpectrum` / `exists_eigenvalues_eq_of_mem_realSpectrum` — the eigenvalue ↔
  real-spectrum bridge, in both directions.
* `exists_isPositiveSpectralGap` — if some point of the real spectrum lies strictly above the
  ground energy, there is a smallest such point and hence a positive spectral gap.

Reference for the consumer: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §6.2 Theorem 6.3.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L N : ℕ}

/-! ### The eigenvalue ↔ real-spectrum bridge -/

/-- Each Hermitian eigenvalue of a chain operator is realised by a nonzero eigenvector (a member of
the eigenvector basis), hence lies in its real spectrum. -/
theorem eigenvalues_mem_realSpectrum {H : ManyBodyOpS (Fin L) N} (hH : H.IsHermitian)
    (i : Fin L → Fin (N + 1)) : hH.eigenvalues i ∈ realSpectrum H := by
  refine ⟨⇑(hH.eigenvectorBasis i), ?_, ?_⟩
  · intro h
    exact hH.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero (p := 2)).mp h)
  · rw [hH.mulVec_eigenvectorBasis i]; exact (Complex.coe_smul _ _).symm

/-- Every element of the real spectrum of a Hermitian chain operator is one of its Hermitian
eigenvalues. -/
theorem exists_eigenvalues_eq_of_mem_realSpectrum {H : ManyBodyOpS (Fin L) N}
    (hH : H.IsHermitian) {E : ℝ} (hE : E ∈ realSpectrum H) : ∃ j, hH.eigenvalues j = E := by
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ := hE
  have h_has : Module.End.HasEigenvalue (Matrix.toLin' H) (E : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hΦ_ne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ_eig
  have h_spec : (E : ℂ) ∈ spectrum ℂ (Matrix.toLin' H) := h_has.mem_spectrum
  rw [Matrix.spectrum_toLin'] at h_spec
  have h_real : E ∈ spectrum ℝ H := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]; exact h_spec
  rw [hH.spectrum_real_eq_range_eigenvalues] at h_real
  obtain ⟨j, hj⟩ := h_real
  exact ⟨j, hj⟩

/-! ### The first excited eigenvalue -/

/-- If `E₀` is the ground energy of a Hermitian chain operator `H` and *some* point of the real
spectrum lies strictly above `E₀`, then there is a smallest such point `E₁`, and `H` has the
positive spectral gap `E₁ − E₀`. -/
theorem exists_isPositiveSpectralGap {H : ManyBodyOpS (Fin L) N} (hH : H.IsHermitian) {E₀ : ℝ}
    (hground : IsGroundEnergy H E₀) (hgt : ∃ E ∈ realSpectrum H, E₀ < E) :
    ∃ E₁ : ℝ, E₁ ∈ realSpectrum H ∧ E₀ < E₁ ∧ (∀ E ∈ realSpectrum H, E₀ < E → E₁ ≤ E) ∧
      IsPositiveSpectralGap H (E₁ - E₀) := by
  classical
  obtain ⟨E, hE_spec, hE_gt⟩ := hgt
  obtain ⟨i₀, hi₀eq⟩ := exists_eigenvalues_eq_of_mem_realSpectrum hH hE_spec
  have hi₀ : E₀ < hH.eigenvalues i₀ := by rw [hi₀eq]; exact hE_gt
  set S : Finset (Fin L → Fin (N + 1)) := Finset.univ.filter (fun i => E₀ < hH.eigenvalues i)
    with hSdef
  have hi₀S : i₀ ∈ S := by rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have himg_ne : (S.image hH.eigenvalues).Nonempty := ⟨_, Finset.mem_image_of_mem _ hi₀S⟩
  set E₁ := (S.image hH.eigenvalues).min' himg_ne with hE₁def
  obtain ⟨i₁, hi₁S, hi₁⟩ := Finset.mem_image.mp ((S.image hH.eigenvalues).min'_mem himg_ne)
  have hE₀E₁ : E₀ < E₁ := by
    rw [hE₁def, ← hi₁]
    rw [hSdef] at hi₁S
    exact (Finset.mem_filter.mp hi₁S).2
  have hE₁_spec : E₁ ∈ realSpectrum H := by
    rw [hE₁def, ← hi₁]; exact eigenvalues_mem_realSpectrum hH i₁
  have hE₁_min : ∀ F ∈ realSpectrum H, E₀ < F → E₁ ≤ F := by
    intro F hF hF₀
    obtain ⟨j, hj⟩ := exists_eigenvalues_eq_of_mem_realSpectrum hH hF
    rw [← hj]
    refine (S.image hH.eigenvalues).min'_le _ (Finset.mem_image_of_mem _ ?_)
    rw [hSdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj]; exact hF₀⟩
  exact ⟨E₁, hE₁_spec, hE₀E₁, hE₁_min, E₀, E₁, hground, hE₁_spec, hE₀E₁, rfl, hE₁_min⟩

end LatticeSystem.Quantum
