import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLMCoreSectors

/-!
# SU(2)-point global uniqueness from the MLM endpoint — core eigenvalue endpoint

Continued from `Theorem24SU2GlobalUniquenessFromMLMCoreSectors.lean` (the
balanced-sector setup, zero-Casimir transfer bridges, the singlet-image
obstruction, and the strict outside-sector ordering / ladder obstruction).
This file carries the spectral endpoint used by Tasaki §2.5 Theorem 2.4
obligation (2): the Hermitian-minimum identification from a common-energy lower
bound and the full-eigenspace `finrank <= 1` simplicity results.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3 and 2.4, pp. 42-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Common-energy lower bound identifies the Hermitian minimum**: if a
Hermitian matrix has a non-zero eigenvector at a real energy `μ`, and every
non-zero real-energy eigenvector has energy at least `μ`, then its Hermitian
minimum eigenvalue is exactly `μ`.

This is the spectral bridge used to connect the Theorem 2.3 common MLM energy
to the `hermitianMinEigenvalue` endpoint consumed by Theorem 2.4. -/
theorem hermitianMinEigenvalue_eq_common_of_eigenvector_and_global_lower
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℝ} {Φ : n → ℂ} (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : M.mulVec Φ = (μ : ℂ) • Φ)
    (h_global_lower : ∀ {μ' : ℝ} {Ψ : n → ℂ}, Ψ ≠ 0 →
      M.mulVec Ψ = (μ' : ℂ) • Ψ → μ ≤ μ') :
    hermitianMinEigenvalue hM = μ := by
  have hmin_le : hermitianMinEigenvalue hM ≤ μ :=
    hermitian_min_eigenvalue_le_of_eigenvector_exists hM hΦ_ne hΦ_eig
  obtain ⟨Ψ, hΨ_ne, hΨ_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hM
  have hle_min : μ ≤ hermitianMinEigenvalue hM :=
    h_global_lower hΨ_ne hΨ_eig
  exact le_antisymm hmin_le hle_min

/-- **The Theorem 2.3 common energy is the full Heisenberg Hermitian minimum**.
Given the structural Theorem 2.3 predicate and its physical hypotheses, the
common MLM energy `μ` coincides with the Hermitian minimum eigenvalue of the
full isotropic Heisenberg Hamiltonian.  The theorem also returns the sector
ground-state family and the global lower-bound callback, because the endpoint
uniqueness proof consumes those witnesses next. -/
theorem exists_tasaki23_common_energy_eq_hermitianMinEigenvalue
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
        [Nonempty (magConfigS V N M)] →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ σ, 0 < v σ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
            (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
            (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
            (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
            μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
              ∀ τ : magConfigS V N M,
                (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') := by
  classical
  obtain ⟨μ, hsector, hglobal⟩ :=
    hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict hN hcardA hcardB
  set M0 :=
    min (Finset.univ.filter (fun x : V => A x = true)).card
      (Finset.univ.filter (fun x : V => (! A x) = true)).card * N
    with hM0def
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
    rw [hM0def]
    exact tasaki23GroundStateSectors_left_mem A N
  haveI : Nonempty (magConfigS V N M0) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v0, _hμ_lt, hv0_pos, hΦ0_eig, _huniq0⟩ := hsector M0 hM0_mem
  set Φ0 : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N M0 =>
      (((marshallSignS A τ.1).re * v0 τ : ℝ) : ℂ))
    with hΦ0def
  have hΦ0_ne : Φ0 ≠ 0 := by
    intro hzero
    let τ : magConfigS V N M0 := Classical.arbitrary _
    have hτ_zero := congrFun hzero τ.1
    rw [hΦ0def, magSectorEmbedding_apply_subtype] at hτ_zero
    have hreal_zero : (marshallSignS A τ.1).re * v0 τ = 0 := by
      exact_mod_cast congrArg Complex.re hτ_zero
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv0_zero : v0 τ = 0 := by
      calc
        v0 τ = ((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) * v0 τ := by
          rw [hsq, one_mul]
        _ = (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v0 τ) := by ring
        _ = 0 := by rw [hreal_zero, mul_zero]
    exact (ne_of_gt (hv0_pos τ)) hv0_zero
  have hmin_eq :
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ :=
    hermitianMinEigenvalue_eq_common_of_eigenvector_and_global_lower
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N)
      hΦ0_ne (by simpa [Φ0, hΦ0def] using hΦ0_eig)
      (fun hΨ_ne hΨ_eig => hglobal hΨ_ne hΨ_eig)
  exact ⟨μ, hmin_eq, hsector, hglobal⟩

/-- **Full SU(2) eigenspace simplicity from sector support and sector PF**:
if every full Heisenberg eigenvector at `μ` lies in the magnetization subspace
corresponding to sector `M`, then the sector-matrix `finrank <= 1` bound at
`μ` transfers to the full Hilbert-space eigenspace at `μ`.

This is the endpoint bridge that replaces the older route through a separate
`finrank <= 2` hypothesis.  The remaining mathematical task is to prove the
sector-support hypothesis from the MLM/Casimir strict outside-sector argument. -/
theorem heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_sector_support
    (J : V → V → ℂ) (M : ℕ) (μ : ℂ)
    (h_support : ∀ {Ψ : (V → Fin (N + 1)) → ℂ},
      (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ →
      Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) μ) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := V) J N)) μ) ≤ 1 := by
  classical
  set E := End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
    with hEdef
  set A :=
    magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ))
    with hAdef
  have h_inf_le :
      finrank ℂ ↥(E ⊓ A) ≤ 1 := by
    subst E
    subst A
    exact heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
      (Λ := V) (N := N) J M μ h_sector_pf
  have h_subset : E ≤ A := by
    intro Ψ hΨ
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply] at hΨ
    rw [hAdef]
    exact h_support hΨ
  have h_inf_eq : E ⊓ A = E := inf_eq_left.mpr h_subset
  rw [h_inf_eq] at h_inf_le
  simpa [hEdef] using h_inf_le

/-- **Sector support from vanishing outside projections**: if every magnetization-sector
projection of `Ψ` outside `M0` is zero, then `Ψ` lies in the centered
magnetization subspace corresponding to `M0`. -/
theorem mem_magSubspaceS_of_magSectorProjection_eq_zero_off_singleton
    (M0 : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (h_projection_zero : ∀ M : ℕ, M ≠ M0 →
      magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0) :
    Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) := by
  classical
  rw [eq_sum_magSectorEmbedding_magSectorRestriction Ψ]
  refine Submodule.sum_mem _ ?_
  intro M _
  by_cases hM : M = M0
  · subst M
    exact magSectorEmbedding_mem_magSubspaceS (magSectorRestriction (M := M0) Ψ)
  · rw [h_projection_zero M hM]
    exact (magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ))).zero_mem

/-- **Full SU(2) eigenspace simplicity from outside-projection exclusion**:
if every eigenvector at `μ` has zero projection to all sectors outside `M0`,
then the sector-matrix `finrank <= 1` bound in `M0` transfers to the full
Heisenberg eigenspace at `μ`. -/
theorem heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_outside_projection_zero
    (J : V → V → ℂ) (M0 : ℕ) (μ : ℂ)
    (h_projection_zero : ∀ {Ψ : (V → Fin (N + 1)) → ℂ},
      (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ →
      ∀ M : ℕ, M ≠ M0 →
        magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) μ) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := V) J N)) μ) ≤ 1 :=
  heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_sector_support
    J M0 μ
    (fun hΨ => mem_magSubspaceS_of_magSectorProjection_eq_zero_off_singleton
      (V := V) (N := N) M0 (h_projection_zero hΨ))
    h_sector_pf

/-- **Outside-sector strict lower bound kills outside projections**: suppose
every real sector eigenvalue outside `M0` is strictly above `μ`.  Then a full
Heisenberg eigenvector at `μ` has zero projection to every outside sector.

This isolates the remaining Casimir/MLM ordering obligation in the exact form
needed by the SU(2)-endpoint uniqueness bridge. -/
theorem heisenbergHamiltonianS_outside_projection_zero_of_strict_sector_lower
    (J : V → V → ℂ) (M0 : ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (h_strict_outside : ∀ M : ℕ, M ≠ M0 → [Nonempty (magConfigS V N M)] →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ < μM)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ)
    (M : ℕ) (hM_ne : M ≠ M0) :
    magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 := by
  classical
  by_cases hW_zero : magSectorRestriction (M := M) Ψ = 0
  · rw [hW_zero, magSectorEmbedding_zero]
  · haveI : Nonempty (magConfigS V N M) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hW_zero (funext (fun τ => (h.false τ).elim))
    have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (magSectorRestriction (M := M) Ψ) =
        (μ : ℂ) • magSectorRestriction (M := M) Ψ :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        J hΨ
    obtain ⟨φ, hφ_ne, hφ⟩ :
        ∃ φ : magConfigS V N M → ℝ, φ ≠ 0 ∧
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ := by
      by_cases hre : (fun σ => (magSectorRestriction (M := M) Ψ σ).re) =
          (0 : magConfigS V N M → ℝ)
      · refine ⟨fun σ => (magSectorRestriction (M := M) Ψ σ).im, ?_,
          heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
            N hJ_real hW_eig⟩
        intro him
        apply hW_zero
        funext τ
        have hr := congrFun hre τ
        have hi := congrFun him τ
        simp only [Pi.zero_apply] at hr hi ⊢
        exact Complex.ext hr hi
      · exact ⟨fun σ => (magSectorRestriction (M := M) Ψ σ).re, hre,
          heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
            N hJ_real hW_eig⟩
    have hlt : μ < μ := h_strict_outside M hM_ne hφ_ne hφ
    exact (lt_irrefl μ hlt).elim

/-- **Full SU(2) eigenspace simplicity from strict outside-sector ordering**:
if the balanced sector has sector-matrix `finrank <= 1` at `μ` and every
outside sector has all real eigenvalues strictly above `μ`, then the full
Heisenberg eigenspace at `μ` has `finrank <= 1`. -/
theorem heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower
    (J : V → V → ℂ) (M0 : ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (h_strict_outside : ∀ M : ℕ, M ≠ M0 → [Nonempty (magConfigS V N M)] →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ < μM)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) (μ : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 :=
  heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_outside_projection_zero
    J M0 (μ : ℂ)
    (fun hΨ M hM_ne =>
      heisenbergHamiltonianS_outside_projection_zero_of_strict_sector_lower
        (V := V) (N := N) J M0 hJ_real h_strict_outside hΨ M hM_ne)
    h_sector_pf

end LatticeSystem.Quantum
