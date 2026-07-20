/-
Model-independent spectral infrastructure for many-body chain operators.

Everything here is stated for an arbitrary chain operator `H : ManyBodyOpS (Fin L) N`; no model,
no spin value and no chain length is fixed.  The eigenvalue ↔ `realSpectrum` bridge and the
first-excited-eigenvalue constructor are shared by the Lieb–Schultz–Mattis ring gap (Tasaki §6.2
Theorem 6.3) and by Knabe's finite-size criterion for the AKLT gap (Tasaki §7.1.4, pp. 188–190;
S. Knabe, *Energy gaps and elementary excitations for certain VBS-quantum antiferromagnets*,
J. Stat. Phys. **52** (1988), 627–638).
-/
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Generic spectral lemmas for many-body chain operators

For a Hermitian chain operator `H : ManyBodyOpS (Fin L) N` this module relates the Hermitian
eigenvalue family `hH.eigenvalues` to the `realSpectrum` of `H`
(`Quantum/SpinS/HaldaneConjecture.lean`), constructs the first excited eigenvalue, and records the
two operator-inequality tools used by gap arguments.

* `eigenvalues_mem_realSpectrum` / `exists_eigenvalues_eq_of_mem_realSpectrum` — the eigenvalue ↔
  real-spectrum bridge in both directions.
* `exists_isPositiveSpectralGap` — if some point of the real spectrum lies strictly above the
  ground energy, there is a smallest such point and hence a positive spectral gap.
* `realSpectrum_nonneg_of_posSemidef` — a positive-semidefinite operator has nonnegative spectrum.
* `realSpectrum_ge_of_sq_sub_smul_posSemidef` — **the spectral step of Knabe's argument**: from
  `H ≥ 0` and `H² − γH ≥ 0` every nonzero spectral point is `≥ γ`.
* `isPositiveSpectralGap_affine` / `isGroundEnergy_affine` — transport of the gap and of the ground
  energy along `H ↦ aH + b·1` with `a > 0`, which is how a projector-sum normalisation of a
  Hamiltonian is converted back to the physical normalisation.

References: S. Knabe, J. Stat. Phys. **52** (1988), 627–638; Hal Tasaki, *Physics and Mathematics
of Quantum Many-Body Systems* (1st ed., Springer, 2020), §7.1.4, pp. 188–190.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

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

/-! ### Positive semidefiniteness and Knabe's spectral step -/

/-- A positive-semidefinite chain operator has nonnegative real spectrum: an eigenvector `Φ` for the
real eigenvalue `E` gives `⟨Φ|H|Φ⟩ = E‖Φ‖² ≥ 0` with `‖Φ‖² > 0`. -/
theorem realSpectrum_nonneg_of_posSemidef {H : ManyBodyOpS (Fin L) N} (hH : H.PosSemidef)
    {E : ℝ} (hE : E ∈ realSpectrum H) : 0 ≤ E := by
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ := hE
  have hpos : (0 : ℂ) < star Φ ⬝ᵥ Φ := Matrix.dotProduct_star_self_pos_iff.mpr hΦ_ne
  have hnn : (0 : ℂ) ≤ star Φ ⬝ᵥ H.mulVec Φ := hH.dotProduct_mulVec_nonneg Φ
  rw [hΦ_eig, dotProduct_smul, smul_eq_mul] at hnn
  have hre : 0 ≤ E * (star Φ ⬝ᵥ Φ).re := by
    have h := (Complex.le_def.mp hnn).1
    rwa [Complex.zero_re, Complex.re_ofReal_mul] at h
  have hcre : 0 < (star Φ ⬝ᵥ Φ).re := (Complex.lt_def.mp hpos).1
  nlinarith [hre, hcre]

/-- **The spectral step of Knabe's argument** (Knabe 1988; Tasaki §7.1.4, pp. 188–190).  If a chain
operator satisfies `H ≥ 0` and `H² − γH ≥ 0`, then every *nonzero* point `E` of its real spectrum
obeys `γ ≤ E`.  Indeed the same eigenvector puts `E² − γE` in the real spectrum of `H² − γH`, so
`E² − γE ≥ 0`, while `E > 0`; dividing by `E` gives `γ ≤ E`.  This is what turns an operator
inequality `H² ≥ γH` for a frustration-free projector sum into a lower bound on its gap. -/
theorem realSpectrum_ge_of_sq_sub_smul_posSemidef {H : ManyBodyOpS (Fin L) N} {γ : ℝ}
    (hH : H.PosSemidef) (hK : (H * H - (γ : ℂ) • H).PosSemidef)
    {E : ℝ} (hE : E ∈ realSpectrum H) (hE0 : E ≠ 0) : γ ≤ E := by
  have hEpos : 0 < E :=
    lt_of_le_of_ne (realSpectrum_nonneg_of_posSemidef hH hE) (Ne.symm hE0)
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ := hE
  have hKspec : E * E - γ * E ∈ realSpectrum (H * H - (γ : ℂ) • H) := by
    refine ⟨Φ, hΦ_ne, ?_⟩
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hΦ_eig, Matrix.mulVec_smul, hΦ_eig,
      Matrix.smul_mulVec, hΦ_eig, smul_smul, smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  have hKnn : 0 ≤ E * E - γ * E := realSpectrum_nonneg_of_posSemidef hK hKspec
  nlinarith [hKnn, hEpos]

/-! ### Affine transport of the gap and of the ground energy -/

/-- The action of the affine combination `aH + b·1` on a vector, split into its two pieces. -/
private theorem affine_mulVec {H : ManyBodyOpS (Fin L) N} {a b : ℝ}
    (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    ((a : ℂ) • H + (b : ℂ) • (1 : ManyBodyOpS (Fin L) N)).mulVec Φ
      = (a : ℂ) • H.mulVec Φ + (b : ℂ) • Φ := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The real spectrum transforms along the affine map `E ↦ aE + b` (`a ≠ 0`), with the *same*
eigenvector: `aE + b` is an eigenvalue of `aH + b·1` exactly when `E` is one of `H`. -/
private theorem mem_realSpectrum_affine_iff {H : ManyBodyOpS (Fin L) N} {a b E : ℝ} (ha : a ≠ 0) :
    a * E + b ∈ realSpectrum ((a : ℂ) • H + (b : ℂ) • (1 : ManyBodyOpS (Fin L) N))
      ↔ E ∈ realSpectrum H := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  constructor
  · rintro ⟨Φ, hΦ_ne, hΦ_eig⟩
    refine ⟨Φ, hΦ_ne, ?_⟩
    rw [affine_mulVec Φ] at hΦ_eig
    have hΦ_eig' : (a : ℂ) • H.mulVec Φ = ((a : ℂ) * (E : ℂ)) • Φ := by
      rw [eq_sub_of_add_eq hΦ_eig, ← sub_smul]
      congr 1
      push_cast
      ring
    have key : (a : ℂ) • H.mulVec Φ = (a : ℂ) • ((E : ℂ) • Φ) := by
      rw [hΦ_eig', ← smul_smul]
    exact smul_right_injective ((Fin L → Fin (N + 1)) → ℂ) ha' key
  · rintro ⟨Φ, hΦ_ne, hΦ_eig⟩
    refine ⟨Φ, hΦ_ne, ?_⟩
    rw [affine_mulVec Φ, hΦ_eig, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- **Affine transport of the gap.**  For `a > 0`, the operator `aH + b·1` has the spectral gap
`a · gap` whenever `H` has the spectral gap `gap`: the spectrum is the affine image `E ↦ aE + b`,
which preserves the order (`a > 0`) and cancels the shift `b` in the difference `E₁ − E₀`. -/
theorem isPositiveSpectralGap_affine {H : ManyBodyOpS (Fin L) N} {a b gap : ℝ} (ha : 0 < a)
    (h : IsPositiveSpectralGap H gap) :
    IsPositiveSpectralGap ((a : ℂ) • H + (b : ℂ) • (1 : ManyBodyOpS (Fin L) N)) (a * gap) := by
  obtain ⟨E₀, E₁, ⟨hE₀_spec, hE₀_min⟩, hE₁_spec, hlt, hgap, hmin⟩ := h
  have hback : ∀ F : ℝ,
      F ∈ realSpectrum ((a : ℂ) • H + (b : ℂ) • (1 : ManyBodyOpS (Fin L) N)) →
        (F - b) / a ∈ realSpectrum H ∧ a * ((F - b) / a) + b = F := by
    intro F hF
    have hrw : a * ((F - b) / a) + b = F := by field_simp; ring
    exact ⟨(mem_realSpectrum_affine_iff ha.ne').mp (by rw [hrw]; exact hF), hrw⟩
  refine ⟨a * E₀ + b, a * E₁ + b, ⟨(mem_realSpectrum_affine_iff ha.ne').mpr hE₀_spec, ?_⟩,
    (mem_realSpectrum_affine_iff ha.ne').mpr hE₁_spec,
    by linarith [mul_lt_mul_of_pos_left hlt ha], by rw [hgap]; ring, ?_⟩
  · intro F hF
    obtain ⟨hmem, hrw⟩ := hback F hF
    have hle := hE₀_min _ hmem
    linarith [mul_le_mul_of_nonneg_left hle ha.le]
  · intro F hF hF₀
    obtain ⟨hmem, hrw⟩ := hback F hF
    have hmul : a * E₀ < a * ((F - b) / a) := by linarith
    have hle := hmin _ hmem (lt_of_mul_lt_mul_left hmul ha.le)
    linarith [mul_le_mul_of_nonneg_left hle ha.le]

/-- **Affine transport of the ground energy.**  For `a > 0` the ground energy of `aH + b·1` is the
affine image `a E₀ + b` of the ground energy of `H`.  Together with `isPositiveSpectralGap_affine`
this carries the spectral data of a projector-sum normalisation over to the physical
normalisation of the same Hamiltonian. -/
theorem isGroundEnergy_affine {H : ManyBodyOpS (Fin L) N} {a b E₀ : ℝ} (ha : 0 < a)
    (h : IsGroundEnergy H E₀) :
    IsGroundEnergy ((a : ℂ) • H + (b : ℂ) • (1 : ManyBodyOpS (Fin L) N)) (a * E₀ + b) := by
  obtain ⟨hE₀_spec, hE₀_min⟩ := h
  refine ⟨(mem_realSpectrum_affine_iff ha.ne').mpr hE₀_spec, ?_⟩
  intro F hF
  have hrw : a * ((F - b) / a) + b = F := by field_simp; ring
  have hmem : (F - b) / a ∈ realSpectrum H :=
    (mem_realSpectrum_affine_iff ha.ne').mp (by rw [hrw]; exact hF)
  have hle := hE₀_min _ hmem
  linarith [mul_le_mul_of_nonneg_left hle ha.le]

end LatticeSystem.Quantum
