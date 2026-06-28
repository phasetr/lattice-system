/-
Tasaki §6.2 Theorem 6.3: the Lieb–Schultz–Mattis / Affleck–Lieb spectral gap (capstone).

Assembling the ground-state data of the antiferromagnetic Heisenberg ring (uniqueness, total-`Ŝ³`
neutrality), the twist-operator trial-energy bound (Lemma 6.1), the ground/twist orthogonality
(Lemma 6.2), and the generic Courant–Fischer second-eigenvalue bound, the half-odd-integer ring has a
positive spectral gap bounded by `8π²S²/L`.  This discharges the axiom
`lieb_schultz_mattis_affleck_lieb`.
-/
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGroundData
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisOrthogonality
import LatticeSystem.Quantum.SpinS.HermitianSecondEigenvalue
import LatticeSystem.Quantum.SpinS.HermitianGapExists
import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder

namespace LatticeSystem.Quantum

open Matrix Module

variable {L N : ℕ}

/-- Each Hermitian eigenvalue of the ring Hamiltonian is realised by a nonzero eigenvector, hence
lies in the real spectrum. -/
private theorem afm_eigenvalues_mem_realSpectrum (L N : ℕ) (i : (Fin L → Fin (N + 1))) :
    (afmHeisenbergChainHamiltonianS_isHermitian L N).eigenvalues i ∈
      realSpectrum (afmHeisenbergChainHamiltonianS L N) := by
  set hM := afmHeisenbergChainHamiltonianS_isHermitian L N
  refine ⟨⇑(hM.eigenvectorBasis i), ?_, ?_⟩
  · intro h
    exact hM.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero (p := 2)).mp h)
  · rw [hM.mulVec_eigenvectorBasis i]; exact (Complex.coe_smul _ _).symm

/-- Every element of the real spectrum of the ring Hamiltonian is one of the Hermitian
eigenvalues. -/
private theorem afm_mem_realSpectrum_eq_eigenvalue (L N : ℕ) {E : ℝ}
    (hE : E ∈ realSpectrum (afmHeisenbergChainHamiltonianS L N)) :
    ∃ j, (afmHeisenbergChainHamiltonianS_isHermitian L N).eigenvalues j = E := by
  set hM := afmHeisenbergChainHamiltonianS_isHermitian L N
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ := hE
  have h_has : Module.End.HasEigenvalue (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N))
      (E : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hΦ_ne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ_eig
  have h_spec : (E : ℂ) ∈ spectrum ℂ (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) :=
    h_has.mem_spectrum
  rw [Matrix.spectrum_toLin'] at h_spec
  have h_real : E ∈ spectrum ℝ (afmHeisenbergChainHamiltonianS L N) := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]; exact h_spec
  rw [hM.spectrum_real_eq_range_eigenvalues] at h_real
  obtain ⟨j, hj⟩ := h_real
  exact ⟨j, hj⟩

/-- The LSM trial state is nonzero (the twist operator is unitary). -/
private theorem lsmTrialState_ne_zero (L N : ℕ) {Φ : (Fin L → Fin (N + 1)) → ℂ} (hΦ : Φ ≠ 0) :
    lsmTrialState L N Φ ≠ 0 := by
  intro hcon
  apply hΦ
  have hu := lsmTwistOperator_unitary L N
  calc Φ = (1 : ManyBodyOpS (Fin L) N).mulVec Φ := by rw [Matrix.one_mulVec]
    _ = ((lsmTwistOperator L N).conjTranspose * lsmTwistOperator L N).mulVec Φ := by rw [hu]
    _ = (lsmTwistOperator L N).conjTranspose.mulVec (lsmTrialState L N Φ) := by
        rw [lsmTrialState, Matrix.mulVec_mulVec]
    _ = (lsmTwistOperator L N).conjTranspose.mulVec 0 := by rw [hcon]
    _ = 0 := Matrix.mulVec_zero _

/-- Ground-state uniqueness in operator form, from the one-dimensional eigenspace. -/
private theorem afm_ground_uniqueness (L N : ℕ) {E₀ : ℝ} {Φ_GS : (Fin L → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ_GS ≠ 0)
    (hΦ_eig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS)
    (hfin : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
      (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1) :
    ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
      (afmHeisenbergChainHamiltonianS L N).mulVec Ψ = (E₀ : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ_GS := by
  set E := Module.End.eigenspace (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)
    with hEdef
  have hΦ_mem : Φ_GS ∈ E := by
    rw [hEdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ_eig
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hfin
  obtain ⟨a, ha⟩ := hv ⟨Φ_GS, hΦ_mem⟩
  have ha' : a • (v : (Fin L → Fin (N + 1)) → ℂ) = Φ_GS := by
    have h := congrArg ((↑) : ↥E → (Fin L → Fin (N + 1)) → ℂ) ha; simpa using h
  have ha_ne : a ≠ 0 := fun h0 => hΦ_ne (by rw [← ha', h0, zero_smul])
  intro Ψ hΨ_ne hΨ_eig
  have hΨ_mem : Ψ ∈ E := by
    rw [hEdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΨ_eig
  obtain ⟨b, hb⟩ := hv ⟨Ψ, hΨ_mem⟩
  have hb' : b • (v : (Fin L → Fin (N + 1)) → ℂ) = Ψ := by
    have h := congrArg ((↑) : ↥E → (Fin L → Fin (N + 1)) → ℂ) hb; simpa using h
  exact ⟨b * a⁻¹, by rw [← hb', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]⟩

/-- **Tasaki §6.2 Theorem 6.3 (Lieb–Schultz–Mattis / Affleck–Lieb).**  For the spin-`S`
antiferromagnetic Heisenberg ring of even length `L` with half-odd-integer spin (`N` odd), there is
a positive spectral gap bounded by `8π²S²/L`. -/
theorem lieb_schultz_mattis_affleck_lieb (L N : ℕ) (hL : RingLengthEven L) (hNodd : Odd N) :
    ∃ gap : ℝ, IsPositiveSpectralGap (afmHeisenbergChainHamiltonianS L N) gap ∧
      gap ≤ 8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ) := by
  classical
  obtain ⟨hLeven, hLpos⟩ := hL
  have hL2 : 2 ≤ L := by obtain ⟨r, hr⟩ := hLeven; omega
  have hN : 1 ≤ N := hNodd.pos
  set M := afmHeisenbergChainHamiltonianS L N with hMdef
  set hM := afmHeisenbergChainHamiltonianS_isHermitian L N with hMherm
  obtain ⟨E₀, Φ_GS, hground, hΦ_ne, hΦ_eig, hfin, hstot⟩ :=
    afm_ring_ground_state_data L N hLeven hL2 hN
  -- (A) `E₀` lower-bounds every eigenvalue
  have hle : ∀ i, E₀ ≤ hM.eigenvalues i := fun i =>
    hground.2 _ (afm_eigenvalues_mem_realSpectrum L N i)
  -- (B) the state has dimension ≥ 2
  have hcard : 2 ≤ Fintype.card (Fin L → Fin (N + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ (N + 1) ^ L := Nat.pow_le_pow_left (by omega) L |>.trans'
            (Nat.pow_le_pow_right (by omega) (by omega))
  -- (C) some eigenvalue lies strictly above `E₀`
  obtain ⟨i₀, hi₀⟩ := hermitian_exists_eigenvalue_gt hM hcard hle hfin
  -- (D) `E₁` = least eigenvalue strictly above `E₀`
  set S : Finset (Fin L → Fin (N + 1)) := Finset.univ.filter (fun i => E₀ < hM.eigenvalues i)
    with hSdef
  have hi₀S : i₀ ∈ S := by rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have himg_ne : (S.image hM.eigenvalues).Nonempty := ⟨_, Finset.mem_image_of_mem _ hi₀S⟩
  set E₁ := (S.image hM.eigenvalues).min' himg_ne with hE₁def
  obtain ⟨i₁, hi₁S, hi₁⟩ := Finset.mem_image.mp ((S.image hM.eigenvalues).min'_mem himg_ne)
  have hE₀E₁ : E₀ < E₁ := by
    rw [hE₁def, ← hi₁]
    rw [hSdef] at hi₁S
    exact (Finset.mem_filter.mp hi₁S).2
  have hE₁_spec : E₁ ∈ realSpectrum M := by
    rw [hE₁def, ← hi₁]; exact afm_eigenvalues_mem_realSpectrum L N i₁
  have hE₁_lb : ∀ i, hM.eigenvalues i ≠ E₀ → E₁ ≤ hM.eigenvalues i := by
    intro i hi
    have hgt : E₀ < hM.eigenvalues i := lt_of_le_of_ne (hle i) (Ne.symm hi)
    refine (S.image hM.eigenvalues).min'_le _ (Finset.mem_image_of_mem _ ?_)
    rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
  have hE₁_min : ∀ E ∈ realSpectrum M, E₀ < E → E₁ ≤ E := by
    intro E hE hE₀
    obtain ⟨j, hj⟩ := afm_mem_realSpectrum_eq_eigenvalue L N hE
    rw [← hj]
    refine (S.image hM.eigenvalues).min'_le _ (Finset.mem_image_of_mem _ ?_)
    rw [hSdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj]; exact hE₀⟩
  -- (E) uniqueness ⟹ orthogonality + low trial energy
  have huniq := afm_ground_uniqueness L N hΦ_ne hΦ_eig hfin
  have horth : star Φ_GS ⬝ᵥ lsmTrialState L N Φ_GS = 0 :=
    lsm_ground_twist_orthogonal L N hLpos hNodd Φ_GS E₀ hΦ_ne hΦ_eig hground huniq hstot
  have hLSM_ne : lsmTrialState L N Φ_GS ≠ 0 := lsmTrialState_ne_zero L N hΦ_ne
  have henergy : expectationRatioRe M (lsmTrialState L N Φ_GS) - E₀ ≤
      8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ) :=
    lsm_energy_bound L N hLpos Φ_GS E₀ hΦ_ne hΦ_eig hground
  -- (F) second-eigenvalue bound: `E₁ ≤ expectationRatioRe`
  have hD : 0 < (star (lsmTrialState L N Φ_GS) ⬝ᵥ lsmTrialState L N Φ_GS).re :=
    dotProduct_star_self_re_pos hLSM_ne
  have hvar := hermitian_second_eigenvalue_variational hM hΦ_eig hΦ_ne hfin hE₁_lb horth
  have hE₁_le_ratio : E₁ ≤ expectationRatioRe M (lsmTrialState L N Φ_GS) := by
    rw [expectationRatioRe, le_div_iff₀ hD]
    exact hvar
  -- (G) assemble the gap
  refine ⟨E₁ - E₀, ⟨E₀, E₁, hground, hE₁_spec, hE₀E₁, rfl, hE₁_min⟩, ?_⟩
  linarith [hE₁_le_ratio, henergy]

end LatticeSystem.Quantum
