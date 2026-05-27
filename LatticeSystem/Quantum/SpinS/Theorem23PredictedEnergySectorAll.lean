import LatticeSystem.Quantum.SpinS.Theorem23JointPredictedSectors
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique

/-!
# A predicted-energy real sector eigenvector in every admissible sector

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) —
generalising `exists_predictedEnergy_sector_eigenvector` (#3710, extremal sector) to
**every** admissible sector via the joint predicted eigenvector at that sector (#3715).

In each admissible sector `M`, the joint predicted eigenvector `magSectorEmbedding Φ`
(#3715) is a full-space `heisenbergHamiltonianS (bipartiteCoupling A)`-eigenvector at the
predicted toy energy `E` (Casimir energy formula #3673); restricting it to the sector
and taking real/imaginary parts (real coupling) yields a non-zero real eigenvector of
`heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M` at `E`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **A predicted-energy real sector eigenvector in every admissible sector** (for
`|¬A| ≤ |A|`): in each `M ∈ tasaki23GroundStateSectors A N` there is a non-zero
`φ : magConfigS Λ N M → ℝ` with
`heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M · φ = E • φ`,
`E = predicted − s_A(s_A+1) − s_B(s_B+1)`. -/
theorem exists_predictedEnergy_sector_eigenvector_of_mem (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := Λ) A N) :
    ∃ φ : magConfigS Λ N M → ℝ, φ ≠ 0 ∧
      (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ =
        (tasaki23PredictedCasimirValue (V := Λ) A N -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) •
          φ := by
  classical
  set E := tasaki23PredictedCasimirValue (V := Λ) A N -
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)
    with hE
  obtain ⟨Φ, hΦ_ne, hΦ_tot, hΦ_A, hΦ_B⟩ :=
    exists_jointPredictedCasimir_embed_sector (N := N) A horient hM
  -- Casimir energy formula: Ĥ_toy (embed Φ) = (predicted − maxCasA − maxCasB) • (embed Φ).
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A hΦ_tot hΦ_A hΦ_B
  have hval : (((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) - maxCasA A N - maxCasB A N) =
      ((E : ℝ) : ℂ) := by
    rw [hE]; unfold maxCasA maxCasB; push_cast; ring
  rw [hval] at hEnergy
  -- (heisenbergToyHamiltonianS = heisenbergHamiltonianS (bipartiteCoupling A)) (rfl).
  set w : (Λ → Fin (N + 1)) → ℂ := magSectorEmbedding Φ with hw
  have hw_eig : (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec w = ((E : ℝ) : ℂ) • w :=
    hEnergy
  have hw_mag : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS Φ
  -- Restrict to the sector; Re/Im give a real sector eigenvector at E.
  set W := magSectorRestriction (M := M) w with hW
  have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector (bipartiteCoupling A) N M).mulVec W =
      ((E : ℝ) : ℂ) • W :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      (bipartiteCoupling A) hw_eig
  have hW_ne : W ≠ 0 := by
    intro hW0
    apply hΦ_ne
    have hembed := magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS (M := M) hw_mag
    rw [← hembed, ← hW, hW0, magSectorEmbedding_zero]
  have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
    N (bipartiteCoupling_im A) hW_eig
  have him := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
    N (bipartiteCoupling_im A) hW_eig
  obtain ⟨σ₀, hσ₀⟩ := Function.ne_iff.mp hW_ne
  rcases eq_or_ne (W σ₀).re 0 with hre0 | hre0
  · refine ⟨fun σ => (W σ).im, ?_, him⟩
    intro hfun
    apply hσ₀
    have : (W σ₀).im = 0 := congrFun hfun σ₀
    exact Complex.ext hre0 (by rw [this]; rfl)
  · exact ⟨fun σ => (W σ).re, fun hfun => hre0 (congrFun hfun σ₀), hre⟩

end LatticeSystem.Quantum
