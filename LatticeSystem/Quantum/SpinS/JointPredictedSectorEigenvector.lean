import LatticeSystem.Quantum.SpinS.JointDiagonalPredictedEigenvector
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique

/-!
# A real sector eigenvector at the predicted toy energy

Issue #3687 / #3674 (the final obligation of the sound Tasaki §2.5 Theorem 2.3
route, #3542).

The minimal-total-spin joint eigenvector `w*` (#3709) is, by the Casimir
decomposition of the toy Hamiltonian (#3673,
`heisenbergToyHamiltonianS = heisenbergHamiltonianS (bipartiteCoupling A)`), a
full-space eigenvector of the bipartite Heisenberg matrix at the **predicted toy
energy**
`E = predicted − s_A(s_A+1) − s_B(s_B+1)`.
Since `w*` lives in the extremal total-magnetization sector `M = |¬A|·N`
(`= min(|A|,|¬A|)·N` for `|¬A| ≤ |A|`), restricting to that sector and taking real
and imaginary parts (the coupling is real, `bipartiteCoupling_im`) produces a
**non-zero real eigenvector** of `heisenbergHamiltonianSReMatrixOnMagSector` at `E`.

This is exactly the spectral witness consumed by
`tasaki23_toy_sector_groundEnergy_le_of_witness` (#3680): the Perron–Frobenius
sector ground-state energy `μ` then satisfies `μ ≤ E`, discharging the `hμ`
hypothesis of the witness capstone (#3656) and pinning the toy ground state's total
Casimir to the predicted value.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The minimal-total-spin joint eigenvector is a bipartite-Heisenberg eigenvector
at the predicted toy energy** (for `|¬A| ≤ |A|`): a non-zero `w` in the extremal
total-magnetization sector with
`(heisenbergHamiltonianS (bipartiteCoupling A) N) w = E • w`, where
`E = predicted − s_A(s_A+1) − s_B(s_B+1)`. -/
theorem exists_jointPredictedCasimir_witness (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ∃ w : (Λ → Fin (N + 1)) → ℂ, w ≠ 0 ∧
      w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) ∧
      (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec w =
        ((tasaki23PredictedCasimirValue (V := Λ) A N -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1) :
            ℝ) : ℂ) • w := by
  obtain ⟨w, hw_ne, hw_span, hw_ker⟩ := exists_jointDiagonal_totalSpinSOpPlus_kernel A horient
  -- w lies in the joint Casimir eigenspace W (span ⊆ W): sublattice eigen-equations.
  have hw_W : w ∈ jointSublatticeCasimirEigenspace (Λ := Λ) A N :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_jointSublatticeCasimirEigenspace A)))
      hw_span
  obtain ⟨hw_A, hw_B⟩ := hw_W
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_B
  -- w lies in the extremal magnetization sector (span ⊆ magSubspaceS).
  have hw_mag : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_magSubspaceS A))) hw_span
  -- The extremal sector value matches `min(|A|, |¬A|)·N`.
  have hmin : min (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := min_eq_right horient
  have hw_mag' : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      ((min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) := by
    rw [hmin]; exact hw_mag
  -- (Ŝ_tot)² w = predicted, by the extremal highest-weight relation.
  have hw_tot := tasaki23_extremal_highestWeight_totalCasimir_eq_predicted (V := Λ) (N := N) A
    hw_mag' hw_ker
  -- Toy energy: Ĥ_toy w = (γ_tot − γ_A − γ_B) • w (#3673).
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A hw_tot hw_A hw_B
  -- Convert the complex eigenvalue to the real predicted toy energy.
  have hval : (((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) -
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1))) =
      ((tasaki23PredictedCasimirValue (V := Λ) A N -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1) :
          ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval] at hEnergy
  -- `heisenbergToyHamiltonianS A N = heisenbergHamiltonianS (bipartiteCoupling A) N` (rfl).
  exact ⟨w, hw_ne, hw_mag, hEnergy⟩

/-- **A non-zero real sector eigenvector at the predicted toy energy** (for
`|¬A| ≤ |A|`): in the extremal sector `M = |¬A|·N` there is a non-zero
`φ : magConfigS Λ N M → ℝ` with
`heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M · φ = E • φ`,
`E = predicted − s_A(s_A+1) − s_B(s_B+1)`.  This is the spectral witness consumed by
`tasaki23_toy_sector_groundEnergy_le_of_witness`. -/
theorem exists_predictedEnergy_sector_eigenvector (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ∃ φ : magConfigS Λ N
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N) → ℝ, φ ≠ 0 ∧
      (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N)).mulVec φ =
        (tasaki23PredictedCasimirValue (V := Λ) A N -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) •
          φ := by
  classical
  set M := (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hM
  set E := tasaki23PredictedCasimirValue (V := Λ) A N -
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)
    with hE
  obtain ⟨w, hw_ne, hw_mag, hw_eig⟩ := exists_jointPredictedCasimir_witness (N := N) A horient
  -- Restrict w to the sector M; it stays an eigenvector of the complex sector matrix.
  set W := magSectorRestriction (M := M) w with hW
  have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector (bipartiteCoupling A) N M).mulVec W =
      (E : ℂ) • W :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      (bipartiteCoupling A) hw_eig
  -- W ≠ 0: otherwise w = embed(restrict w) = embed 0 = 0.
  have hW_ne : W ≠ 0 := by
    intro hW0
    apply hw_ne
    have hembed := magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS (M := M) hw_mag
    rw [← hembed, ← hW, hW0, magSectorEmbedding_zero]
  -- Real and imaginary parts are real sector eigenvectors at E.
  have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
    N (bipartiteCoupling_im A) hW_eig
  have him := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
    N (bipartiteCoupling_im A) hW_eig
  -- At least one of Re W, Im W is non-zero.
  obtain ⟨σ₀, hσ₀⟩ := Function.ne_iff.mp hW_ne
  rcases eq_or_ne (W σ₀).re 0 with hre0 | hre0
  · -- Re W σ₀ = 0 ⟹ Im W σ₀ ≠ 0 (else W σ₀ = 0).
    refine ⟨fun σ => (W σ).im, ?_, him⟩
    intro hfun
    apply hσ₀
    have : (W σ₀).im = 0 := congrFun hfun σ₀
    exact Complex.ext hre0 (by rw [this]; rfl)
  · exact ⟨fun σ => (W σ).re, fun hfun => hre0 (congrFun hfun σ₀), hre⟩

end LatticeSystem.Quantum
