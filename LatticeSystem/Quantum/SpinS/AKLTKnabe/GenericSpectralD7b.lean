import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Gate D7b (block ④-I): generic spectral infrastructure for the Knabe gap

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) contains the
*size- and model-independent* spectral lemmas that the AKLT gap
assembly (block ④-III) consumes.  Nothing here mentions the AKLT model, spin `1`, or a ring
length: everything is stated for an arbitrary chain operator `H : ManyBodyOpS (Fin L) N` and its
`realSpectrum` (`Quantum/SpinS/HaldaneConjecture.lean:56`).

* **S1** `eigenvalues_mem_realSpectrum` / `exists_eigenvalues_eq_of_mem_realSpectrum` — the
  eigenvalue ↔ real-spectrum bridge for an arbitrary Hermitian chain operator.  These generalise
  the two `private` helpers `afm_eigenvalues_mem_realSpectrum` /
  `afm_mem_realSpectrum_eq_eigenvalue` of `Quantum/SpinS/LiebSchultzMattisRingGap.lean:24,35`,
  which are the same statements specialised to `afmHeisenbergChainHamiltonianS L N`; when this
  block lands in production those two are to be deleted and their two call sites rewired here
  (no duplicate declarations).
* **S2** `exists_isPositiveSpectralGap` — the generic *first excited eigenvalue* constructor,
  extracted from the inline block (D) of `LiebSchultzMattisRingGap.lean:117–140`.
* **S3** `realSpectrum_nonneg_of_posSemidef` — a positive-semidefinite operator has nonnegative
  real spectrum.
* **S4** `realSpectrum_ge_of_sq_sub_smul_posSemidef` — **Knabe's spectral step**: if `H ≥ 0` and
  `H² − γH ≥ 0`, then every nonzero point of the real spectrum is `≥ γ`.  This is the only
  mathematically new statement of the block; neither mathlib nor this repository has it.
* **S5** `isPositiveSpectralGap_affine` — transport of the spectral gap along `H ↦ aH + b·1`
  with `a > 0`: the gap is multiplied by `a` and is unaffected by the shift `b`.  This is what
  converts the projector-sum gap of eq. (7.1.7) into the gap of the (7.1.1) normalisation.
* **S6** `isGroundEnergy_affine` — the companion transport of the *ground energy* along
  `H ↦ aH + b·1` with `a > 0`; block ④-III needs both, since the (7.1.1) ground energy `−(2/3)L`
  is the affine image of the projector-sum ground energy `0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4 (Knabe's argument), pp. 188–190.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {L N : ℕ}

/-! ### S1 — the eigenvalue ↔ real-spectrum bridge (generic Hermitian) -/

/-- **S1a.**  Each Hermitian eigenvalue of a chain operator is realised by a nonzero eigenvector,
hence lies in its real spectrum.  (Generic form of the `private`
`afm_eigenvalues_mem_realSpectrum` of `LiebSchultzMattisRingGap.lean:24`.) -/
theorem eigenvalues_mem_realSpectrum {H : ManyBodyOpS (Fin L) N} (hH : H.IsHermitian)
    (i : Fin L → Fin (N + 1)) : hH.eigenvalues i ∈ realSpectrum H := by
  refine ⟨⇑(hH.eigenvectorBasis i), ?_, ?_⟩
  · intro h
    exact hH.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero (p := 2)).mp h)
  · rw [hH.mulVec_eigenvectorBasis i]; exact (Complex.coe_smul _ _).symm

/-- **S1b.**  Every element of the real spectrum of a Hermitian chain operator is one of its
Hermitian eigenvalues.  (Generic form of the `private` `afm_mem_realSpectrum_eq_eigenvalue` of
`LiebSchultzMattisRingGap.lean:35`.) -/
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

/-! ### S2 — the generic first-excited-eigenvalue constructor -/

/-- **S2.**  If `E₀` is the ground energy of a Hermitian chain operator `H` and *some* point of the
real spectrum lies strictly above `E₀`, then there is a smallest such point `E₁`, and `H` has the
positive spectral gap `E₁ − E₀`.  (Generic form of the inline block (D) of
`LiebSchultzMattisRingGap.lean:117–140`.) -/
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

/-! ### S3, S4 — positive semidefiniteness and Knabe's spectral step -/

/-- **S3.**  A positive-semidefinite chain operator has nonnegative real spectrum:
`⟨Φ|H|Φ⟩ = E‖Φ‖² ≥ 0` with `‖Φ‖² > 0`. -/
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

/-- **S4 (Knabe's spectral step).**  If a chain operator satisfies `H ≥ 0` and `H² − γH ≥ 0`, then
every *nonzero* point `E` of its real spectrum obeys `γ ≤ E`.  Indeed the same eigenvector puts
`E² − γE` in the real spectrum of `H² − γH`, so `E² − γE ≥ 0` by S3, while `E > 0` by S3 applied
to `H`.  Tasaki uses this with `γ = 1/10` to convert the Knabe operator inequality
`(Ĥ′)² ≥ (1/10)Ĥ′` into the gap bound. -/
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

/-! ### S5 — affine transport of the spectral gap -/

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
    refine smul_right_injective ((Fin L → Fin (N + 1)) → ℂ) ha' ?_
    change (a : ℂ) • H.mulVec Φ = (a : ℂ) • ((E : ℂ) • Φ)
    rw [hΦ_eig', ← smul_smul]
  · rintro ⟨Φ, hΦ_ne, hΦ_eig⟩
    refine ⟨Φ, hΦ_ne, ?_⟩
    rw [affine_mulVec Φ, hΦ_eig, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- **S5 (affine transport of the gap).**  For `a > 0`, the operator `aH + b·1` has the spectral
gap `a · gap` whenever `H` has the spectral gap `gap`: the spectrum is the affine image
`E ↦ aE + b`, which preserves the order (`a > 0`) and cancels the shift `b` in the difference
`E₁ − E₀`. -/
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

/-- **S6 (affine transport of the ground energy).**  For `a > 0` the ground energy of `aH + b·1` is
the affine image `a E₀ + b` of the ground energy of `H`.  Together with S5 this is what carries the
projector-sum data of eq. (7.1.7) — ground energy `0` and gap `1/10` — over to the (7.1.1)
normalisation, where the energy becomes `−(2/3)L` and the gap `1/5`. -/
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
