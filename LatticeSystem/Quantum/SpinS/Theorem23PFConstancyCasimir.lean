import LatticeSystem.Quantum.SpinS.Theorem23PFLadderLink

/-!
# Adjacent-sector ground-energy constancy from the predicted total Casimir alone

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3).

The adjacent-sector ground-energy bounds (`Theorem23PFConstancy.lean`) require their
source eigenvector to lie in the *joint* predicted toy ground-state subspace
`bipartiteToyGroundStateSubspacePredicted` — a triple eigenspace of `(Ŝ_tot)²`,
`(Ŝ_A)²`, `(Ŝ_¬A)²`.  But inspection of the ladder link shows that **only the total
Casimir eigenvalue is used** (the sublattice components are extracted but never
consumed): `tasaki23_pf_ladder_link_succ` / `_pred` take a bare total-Casimir
eigen-equation `(Ŝ_tot)² Ψ = γ Ψ` together with the kernel-value mismatch `γ ≠ …`.

This matters for the sound route: the ground state of an *arbitrary* bipartite
antiferromagnetic coupling `J` need not be a sublattice-Casimir eigenvector (the
sublattice operators do not commute with a general `J`), so it is **not** in the
joint subspace.  It does, however, carry the predicted *total* Casimir value (by the
overlap pin, `tasaki23_pf_groundState_casimir_eq_predicted_base` and its
ladder-propagated successors).

This module therefore restates the adjacent-sector bounds and constancy taking the
predicted total-Casimir eigen-equation directly, removing the over-strong joint
membership hypothesis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Adjacent-sector ground-energy bound (lowering) from the predicted total
Casimir**: the lowering bound `tasaki23_pf_sector_energy_succ_le` with its joint
predicted-GS membership replaced by the bare predicted total-Casimir eigen-equation
for the source sector `M`. -/
theorem tasaki23_pf_sector_energy_succ_le_of_casimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ μ' : ℝ} {Φ : magConfigS V N M → ℂ} {w : magConfigS V N (M + 1) → ℝ}
    (hCas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • magSectorEmbedding Φ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ_ne : magSectorEmbedding Φ ≠ 0)
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hw :
      (heisenbergHamiltonianSReMatrixOnMagSector J N (M + 1)).mulVec w =
        μ' • w) :
    μ' ≤ μ := by
  obtain ⟨hH_succ, hne_succ, hmem⟩ :=
    tasaki23_pf_ladder_link_succ hH hCas
      (tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right A N hM hMlt)
      hΦ_ne
  have hmem' :
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
    convert hmem using 2
    push_cast
    ring
  set Ψ := (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) with hΨdef
  set W : magConfigS V N (M + 1) → ℂ := magSectorRestriction (M := M + 1) Ψ with hWdef
  have hembedW : magSectorEmbedding W = Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hmem'
  have hW_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N (M + 1)).mulVec W = (μ : ℂ) • W := by
    apply heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH_succ
    intro σ hσ
    exact magSubspaceS_apply_eq_zero_of_magSumS_ne hmem' hσ
  have hW_ne : W ≠ 0 := by
    intro h0
    apply hne_succ
    rw [← hembedW, h0, magSectorEmbedding_zero]
  obtain ⟨σ0, hσ0⟩ := Function.ne_iff.mp hW_ne
  have hRe :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig
  have hIm :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig
  by_cases hre : (fun σ => (W σ).re) = (0 : magConfigS V N (M + 1) → ℝ)
  · have him_ne : (fun σ => (W σ).im) ≠ 0 := by
      intro h0
      apply hσ0
      apply Complex.ext
      · exact congrFun hre σ0
      · exact congrFun h0 σ0
    exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      him_ne hIm
  · exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      hre hRe

/-- **Adjacent-sector ground-energy bound (raising) from the predicted total
Casimir**: the raising bound `tasaki23_pf_sector_energy_pred_le` with its joint
predicted-GS membership replaced by the bare predicted total-Casimir eigen-equation
for the source sector `M + 1`. -/
theorem tasaki23_pf_sector_energy_pred_le_of_casimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1)
    {μ μ' : ℝ} {Φ : magConfigS V N (M + 1) → ℂ} {w : magConfigS V N M → ℝ}
    (hCas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • magSectorEmbedding Φ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ_ne : magSectorEmbedding Φ ≠ 0)
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hw :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ' • w) :
    μ' ≤ μ := by
  obtain ⟨hH_pred, hne_pred, hmem⟩ :=
    tasaki23_pf_ladder_link_pred hH hCas
      (tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt A N hM hMlt)
      hΦ_ne
  have hmem' :
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    convert hmem using 2
    push_cast
    ring
  set Ψ := (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) with hΨdef
  set W : magConfigS V N M → ℂ := magSectorRestriction (M := M) Ψ with hWdef
  have hembedW : magSectorEmbedding W = Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hmem'
  have hW_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W = (μ : ℂ) • W := by
    apply heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH_pred
    intro σ hσ
    exact magSubspaceS_apply_eq_zero_of_magSumS_ne hmem' hσ
  have hW_ne : W ≠ 0 := by
    intro h0
    apply hne_pred
    rw [← hembedW, h0, magSectorEmbedding_zero]
  obtain ⟨σ0, hσ0⟩ := Function.ne_iff.mp hW_ne
  have hRe :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig
  have hIm :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig
  by_cases hre : (fun σ => (W σ).re) = (0 : magConfigS V N M → ℝ)
  · have him_ne : (fun σ => (W σ).im) ≠ 0 := by
      intro h0
      apply hσ0
      apply Complex.ext
      · exact congrFun hre σ0
      · exact congrFun h0 σ0
    exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      him_ne hIm
  · exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      hre hRe

/-- **Adjacent-sector ground-energy constancy from the predicted total Casimir**:
the constancy step `tasaki23_pf_sector_energy_eq` with both joint predicted-GS
memberships replaced by the bare predicted total-Casimir eigen-equations for the two
Marshall-positive Perron–Frobenius ground states.  This is the sound inductive
constancy step: the per-sector ground states need only carry the predicted *total*
Casimir value, which the overlap pin supplies for an arbitrary bipartite `J`. -/
theorem tasaki23_pf_sector_energy_eq_of_casimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hM1_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt_right :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hMlt_left :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1)
    {μM μM1 : ℝ} {vM : magConfigS V N M → ℝ} {vM1 : magConfigS V N (M + 1) → ℝ}
    (hvM_pos : ∀ σ, 0 < vM σ) (hvM1_pos : ∀ σ, 0 < vM1 σ)
    (hH_M :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)))
    (hH_M1 :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ))) =
        (μM1 : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ)))
    (hRe_M :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM σ) =
        μM • (fun σ => (marshallSignS A σ.1).re * vM σ))
    (hRe_M1 :
      (heisenbergHamiltonianSReMatrixOnMagSector J N (M + 1)).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM1 σ) =
        μM1 • (fun σ => (marshallSignS A σ.1).re * vM1 σ))
    (hCas_M :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)))
    (hCas_M1 :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ))) :
    μM = μM1 := by
  have hmarshall_pos_M : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM_pos σ
  have hmarshall_pos_M1 : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM1 σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM1_pos σ
  have hΦM_ne := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM_pos
  have hΦM1_ne := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM1_pos
  have hle1 : μM1 ≤ μM :=
    tasaki23_pf_sector_energy_succ_le_of_casimir A N c hJ_real hJ_real' hJ_nn hJ_sym
      hJ_bipartite hc_strict hM_mem hMlt_right hCas_M hH_M hΦM_ne
      hmarshall_pos_M1 hRe_M1
  have hle2 : μM ≤ μM1 :=
    tasaki23_pf_sector_energy_pred_le_of_casimir A N c hJ_real hJ_real' hJ_nn hJ_sym
      hJ_bipartite hc_strict hM1_mem hMlt_left hCas_M1 hH_M1 hΦM1_ne
      hmarshall_pos_M hRe_M
  exact le_antisymm hle2 hle1

end LatticeSystem.Quantum
