import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23StructuralSectorLiftCasimir
import LatticeSystem.Quantum.SpinS.Theorem24SU2SymmetricFinrankLeOneFromSectorPF
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector

/-!
# SU(2)-point global uniqueness from the MLM endpoint

This file develops the non-circular SU(2)-endpoint input needed for Tasaki
§2.5 Theorem 2.4 obligation (2).  The proof is routed through the
Marshall-Lieb-Mattis / Perron-Frobenius / Casimir infrastructure from Theorem
2.3, not through the strict-gap wrappers used later in the anisotropic
deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3 and 2.4, pp. 42-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- **Symmetric sublattice sector singleton, membership form**: if the two
Boolean sublattices have equal cardinality, then Tasaki Theorem 2.3's predicted
ground-state sector interval contains exactly `|A| * N`. -/
theorem tasaki23GroundStateSectors_mem_iff_eq_of_card_eq
    (A : V → Bool) (N M : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ↔
      M = (Finset.univ.filter (fun x : V => A x = true)).card * N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  rw [← h_card_eq, min_self, max_self]
  omega

omit [DecidableEq V] in
/-- **Symmetric sublattice sector singleton, finset form**: if the two Boolean
sublattices have equal cardinality, then Theorem 2.3's predicted ground-state
sector set is the singleton `{|A| * N}`. -/
theorem tasaki23GroundStateSectors_eq_singleton_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23GroundStateSectors (V := V) A N =
      {((Finset.univ.filter (fun x : V => A x = true)).card * N)} := by
  ext M
  rw [tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N M h_card_eq,
    Finset.mem_singleton]

omit [DecidableEq V] in
/-- **Symmetric sublattice predicted total spin is zero**: in the balanced
cardinality case, Tasaki Theorem 2.3's predicted total-spin magnitude
`||A| - |not A|| * N / 2` vanishes. -/
theorem tasaki23PredictedTotalSpin_eq_zero_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23PredictedTotalSpin (V := V) A N = 0 := by
  unfold tasaki23PredictedTotalSpin
  rw [h_card_eq, sub_self, abs_zero, zero_mul]

omit [DecidableEq V] in
/-- **Symmetric sublattice predicted Casimir is zero**: in the balanced
cardinality case, the predicted total spin is `0`, so the predicted
total-Casimir value `S(S+1)` is also `0`. -/
theorem tasaki23PredictedCasimirValue_eq_zero_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23PredictedCasimirValue (V := V) A N = 0 := by
  rw [tasaki23PredictedCasimirValue,
    tasaki23PredictedTotalSpin_eq_zero_of_card_eq A N h_card_eq]
  ring

/-- **Symmetric-sector lift with zero total Casimir**: the structural
Theorem 2.3 PF/Casimir lift specializes in the balanced-cardinality case to a
full Heisenberg eigenvector whose total-Casimir eigenvalue is `0`.  This is
the equality-case input needed for the strict outside-sector MLM endpoint. -/
theorem tasaki23_sector_lift_and_casimir_zero_of_card_eq
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
      (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hReEig : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ)) :
    ((heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
    ((totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      (0 : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  classical
  have horient :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card := by
    rw [← h_card_eq]
  obtain ⟨hH, hCas⟩ :=
    tasaki23_sector_lift_and_casimir (N := N) A c c_toy horient hsB hM
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hv_pos hReEig
  refine ⟨hH, ?_⟩
  have hpred0 := tasaki23PredictedCasimirValue_eq_zero_of_card_eq (V := V) A N h_card_eq
  simpa [hpred0] using hCas

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

/-- **Packaged MLM-to-SU(2) uniqueness endpoint**: under balanced sublattice
cardinality, the structural Theorem 2.3 predicate identifies its common energy
with the full Heisenberg Hermitian minimum and collapses the admissible band to
the singleton balanced sector.  If, at that common energy, the balanced sector
has Perron--Frobenius `finrank <= 1` and every other sector has strictly larger
real eigenvalues, then the full SU(2)-point ground eigenspace has `finrank <= 1`.

This is the consumer-facing non-circular endpoint for the remaining Theorem 2.4
obligation: the two callbacks are exactly the sector PF simplicity and the
strict MLM/Casimir outside-sector ordering, with no dependence on anisotropic
strict-gap wrappers. -/
theorem exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1)
    (h_strict_outside : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ →
      ∀ M : ℕ,
        M ≠ (Finset.univ.filter (fun x : V => A x = true)).card * N →
        [Nonempty (magConfigS V N M)] →
        ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
          μ < μM) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      tasaki23GroundStateSectors (V := V) A N =
        {((Finset.univ.filter (fun x : V => A x = true)).card * N)} ∧
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 := by
  classical
  set M0 := (Finset.univ.filter (fun x : V => A x = true)).card * N with hM0def
  obtain ⟨μ, hmin_eq, _hsector, _hglobal⟩ :=
    exists_tasaki23_common_energy_eq_hermitianMinEigenvalue A N c hT23
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      hN hcardA hcardB
  have hsectors_singleton :
      tasaki23GroundStateSectors (V := V) A N = {M0} := by
    rw [hM0def]
    exact tasaki23GroundStateSectors_eq_singleton_of_card_eq A N h_card_eq
  have hpf :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) (μ : ℂ)) ≤ 1 := by
    rw [hM0def]
    exact h_sector_pf μ hmin_eq
  have hstrict : ∀ M : ℕ, M ≠ M0 → [Nonempty (magConfigS V N M)] →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ < μM := by
    intro M hM_ne
    rw [hM0def] at hM_ne
    exact h_strict_outside μ hmin_eq M hM_ne
  have huniq :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 :=
    heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower
      (V := V) (N := N) J M0 hJ_real hstrict hpf
  exact ⟨μ, hmin_eq, by simpa [M0, hM0def] using hsectors_singleton, huniq⟩

end LatticeSystem.Quantum
