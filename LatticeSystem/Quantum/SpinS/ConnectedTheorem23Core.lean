import LatticeSystem.Quantum.SpinS.ConnectedSectorIrreducible
import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancyCasimir

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Tasaki §2.5 Theorem 2.3 for a general CONNECTED bipartite coupling

(Issue #4609, PR3): extends the complete-bipartite
`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`
(`Theorem23StructuralGeneralFinal.lean`) to a general *connected* bipartite
coupling `J`, positive only on the edges of a connected bipartite graph `G` and
vanishing off `G`.

## Strategy

The dressed matrix `shiftedDressedSReMatrixOnMagSector A J N c M` depends only on
`J` (not on a graph).  The strict-positivity hypothesis `hJ_pos` of the
complete-bipartite chain flows down *only* through Perron–Frobenius
irreducibility `isIrreducible_shiftedDressedSReMatrixOnMagSector`.  We therefore
parameterise the whole PF-consuming chain by the *irreducibility result*

    `hIrred : ∀ (M) [Nonempty (magConfigS V N M)],
       (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible`

as a hypothesis (the `_of_irreducible` variants below), making each chain lemma
graph-agnostic.  For the connected case we feed
`isIrreducible_shiftedDressedSReMatrixOnMagSector_connected` (PR3 Step 1);
the complete case still feeds `isIrreducible_shiftedDressedSReMatrixOnMagSector`.

The remaining ingredients of the assembly — `tasaki23_general_hOutside`,
`tasaki23_eigenvalue_ge_common`, `tasaki23_pf_sector_energy_eq_of_casimir`, and
the entire toy-coupling Casimir branch — use only `hJ_nn` (non-negativity), which
a connected `J` satisfies, so they are reused unchanged.

## Output

`tasaki_2_5_theorem_2_3_data_of_connected` proves the *data* conclusion of
`tasaki_2_5_theorem_2_3` (the `∃ μ, (per-sector ground states) ∧ (global min)`
body) directly from the connected hypotheses, dropping the complete-bipartite
`hJ_pos` premise (which a connected `J` cannot satisfy).  This is the usable
input for discharging the §4.1 Theorem 4.4 axiom.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobeniusMain

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Base PF layer parameterised by irreducibility -/

/-- **PF positive eigenvector from a supplied irreducibility witness**.
Graph-agnostic variant of `exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector`,
taking the irreducibility of the shifted dressed sector matrix as a hypothesis. -/
theorem exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (r : ℝ) (v : magConfigS V N M → ℝ),
      0 < r ∧ (∀ σ, 0 < v σ) ∧
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v :=
  LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible hIrred

/-- **Dressed-Heisenberg PF positive eigenvector from a supplied irreducibility
witness**. Graph-agnostic variant of
`exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector`. -/
theorem exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v := by
  obtain ⟨r, v, hr_pos, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hIrred
  refine ⟨c - r, v, by linarith, hv_pos, ?_⟩
  exact dressedHeisenbergSReMatrixOnMagSector_mulVec_of_shifted_eigenvec A J N c hmul

/-- **Heisenberg sector Marshall-sign eigenvector from a supplied irreducibility
witness**. Graph-agnostic variant of
`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hIrred
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
      A N hJ_real hmul⟩

/-! ## Eigenvector proportionality / uniqueness parameterised by irreducibility -/

/-- **Shifted-dressed sector eigenvector proportionality from a supplied
irreducibility witness**. Graph-agnostic variant of
`tasaki23_shiftedDressed_sector_eigenvec_proportional`. -/
theorem tasaki23_shiftedDressed_sector_eigenvec_proportional_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {r : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = r • w) :
    ∃ s : ℝ, w = s • v :=
  LatticeSystem.Math.PerronFrobenius.eigenvec_proportional_of_pos_eigenvec hIrred hv hv_pos hw

/-- **Heisenberg sector eigenvector proportionality from a supplied
irreducibility witness**. Graph-agnostic variant of
`tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive`. -/
theorem tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {φ w : magConfigS V N M → ℝ}
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ)
    (hφ_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * φ σ)
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w) :
    ∃ s : ℝ, w = s • φ := by
  have hφs :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hφ)
  have hws :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hw)
  obtain ⟨s, hs⟩ :=
    tasaki23_shiftedDressed_sector_eigenvec_proportional_of_irreducible A c hIrred
      hφs hφ_pos hws
  refine ⟨s, ?_⟩
  funext σ
  have hi := congrFun hs σ
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  calc
    w σ = ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * w σ := by
          rw [hsq, one_mul]
    _ = (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * w σ) := by ring
    _ = (marshallSignS A σ.1).re * (s * ((marshallSignS A σ.1).re * φ σ)) := by rw [hi]
    _ = s * ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re * φ σ) := by ring
    _ = s * φ σ := by rw [hsq, one_mul]

/-- **Shifted-dressed PF positive eigenvector uniqueness from a supplied
irreducibility witness**. Graph-agnostic variant of
`pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector`. -/
theorem pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  LatticeSystem.Math.PerronFrobenius.pos_eigenvec_unique hIrred hv hv_pos hw hw_pos

/-- **Dressed-Heisenberg PF positive eigenvector uniqueness from a supplied
irreducibility witness**. Graph-agnostic variant of
`pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector`. -/
theorem pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v := by
  have hv' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c hv
  have hw' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c hw
  exact pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector_of_irreducible
    (N := N) (M := M) A c hIrred hv' hv_pos hw' hw_pos

/-- **Marshall-positive Heisenberg sector eigenvector uniqueness from a supplied
irreducibility witness**. Graph-agnostic variant of
`marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector`. -/
theorem marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    ∃ r : ℝ, 0 < r ∧ w₂ = r • w₁ := by
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hw₂
  obtain ⟨r, hr_pos, hrel⟩ :=
    pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hIrred hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos
  refine ⟨r, hr_pos, ?_⟩
  funext σ
  have hσ := congrFun hrel σ
  change (marshallSignS A σ.1).re * w₂ σ =
    r * ((marshallSignS A σ.1).re * w₁ σ) at hσ
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  change w₂ σ = r * w₁ σ
  have lhs_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) = w₂ σ := by
    rw [← mul_assoc, hsq, one_mul]
  have rhs_eq : (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) = r * w₁ σ := by
    have hauxr : (marshallSignS A σ.1).re *
        (r * ((marshallSignS A σ.1).re * w₁ σ)) =
      ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * (r * w₁ σ) := by
      ring
    rw [hauxr, hsq, one_mul]
  have h_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) =
    (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) := by
    rw [hσ]
  rw [lhs_eq, rhs_eq] at h_eq
  exact h_eq

/-- **Marshall-positive complex sector eigenvector uniqueness from a supplied
irreducibility witness**. Graph-agnostic variant of
`marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector`. -/
theorem marshallPositive_complexEigenvec_re_unique_heisSMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ₁ μ₂ : ℝ} {W₁ W₂ : magConfigS V N M → ℂ}
    (hW₁ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₁ = (μ₁ : ℂ) • W₁)
    (hW₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₁ σ).re)
    (hW₂ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₂ = (μ₂ : ℂ) • W₂)
    (hW₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₂ σ).re) :
    μ₁ = μ₂ ∧ ∃ r : ℝ, 0 < r ∧ ∀ σ, (W₂ σ).re = r * (W₁ σ).re := by
  have hW₁_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW₁
  have hW₂_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW₂
  have hμ_eq : μ₁ = μ₂ :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  refine ⟨hμ_eq, ?_⟩
  subst hμ_eq
  obtain ⟨r, hr_pos, hrel⟩ :=
    marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hJ_real hIrred hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  exact ⟨r, hr_pos, fun σ => congrFun hrel σ⟩

/-! ## Full-Hilbert existence + bundled MLM parameterised by irreducibility -/

/-- **Complex sector Marshall-positive eigenvector from a supplied irreducibility
witness**. Graph-agnostic variant of
`exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector`. -/
theorem exists_marshallSign_complexEigenvector_heisSMatrixOnMagSector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) =
        (μ : ℂ) • (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hJ_real hIrred
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal N hJ_real hmul⟩

/-- **Full-Hilbert-space Marshall eigenvector existence from a supplied
irreducibility witness**. Graph-agnostic variant of
`exists_marshallSign_eigenvector_heisenbergHamiltonianS_full`. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianS_full_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_complexEigenvector_heisSMatrixOnMagSector_of_irreducible
      (N := N) (M := M) A c hJ_real hIrred
  exact ⟨μ, v, hμ, hv_pos, heisenbergHamiltonianS_mulVec_magSectorEmbedding J _ hmul⟩

/-- **Per-sector existence step from a supplied irreducibility witness**.
Graph-agnostic variant of `tasaki_2_5_theorem_2_3_sector_existence`. -/
theorem tasaki_2_5_theorem_2_3_sector_existence_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianS_full_of_irreducible
      (N := N) (M := M) A c hJ_real hIrred
  refine ⟨μ, v, hμ, hv_pos, hmul, ?_, ?_⟩
  · intro σ hne
    exact magSectorEmbedding_apply_of_not_mem _ hne
  · intro μ' Ψ' hΨ' hΨ'_supp hΨ'_marshall_pos
    have hΨ'_sec :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hΨ' hΨ'_supp
    have hsec_ground :
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) =
          (μ : ℂ) • (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
      funext τ
      change (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ' : magConfigS V N M =>
            (((marshallSignS A τ'.1).re * v τ' : ℝ) : ℂ)) τ =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [← heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype J _ τ]
      have hμembed := congrFun hmul τ.1
      rw [hμembed]
      change ((μ : ℂ) • magSectorEmbedding _) τ.1 =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [Pi.smul_apply, magSectorEmbedding_apply_subtype, smul_eq_mul]
    obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
      marshallPositive_complexEigenvec_re_unique_heisSMatrixOnMagSector_of_irreducible
        (N := N) (M := M) A c hJ_real hJ_real' hIrred hsec_ground (by
          intro τ
          rw [Complex.ofReal_re]
          have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
            marshallSignS_re_sq A τ.1
          rw [← mul_assoc, hsq, one_mul]
          exact hv_pos τ)
        hΨ'_sec hΨ'_marshall_pos
    refine ⟨hμ_eq.symm, r, hr_pos, fun τ => ?_⟩
    have hτ := hrel τ
    change (magSectorRestriction Ψ' τ).re = r * ((marshallSignS A τ.1).re * v τ)
    rw [hτ]
    rw [Complex.ofReal_re]

/-! ## Casimir branch parameterised by irreducibility -/

/-- **PF ground state commuting eigenvector from a supplied irreducibility
witness**. Graph-agnostic variant of
`tasaki23_pf_groundState_commuting_eigenvector`. -/
theorem tasaki23_pf_groundState_commuting_eigenvector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    (B : ManyBodyOpS V N)
    (hHB : Commute (heisenbergHamiltonianS J N) B)
    (h3B : Commute (totalSpinSOp3 V N) B)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    ∃ γ : ℂ,
      B.mulVec (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  set Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hΦdef
  set φ : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * v σ with hφdef
  have hΦ_mem :
      Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS _
  have hΨ_eig :
      (heisenbergHamiltonianS J N).mulVec (B.mulVec Φ) = (μ : ℂ) • B.mulVec Φ :=
    mulVec_preserves_eigenvalue_of_commuteS hHB hH
  have hΨ_mem :
      B.mulVec Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    rw [mem_magSubspaceS_iff] at hΦ_mem ⊢
    exact mulVec_preserves_eigenvalue_of_commuteS h3B hΦ_mem
  have hΨ_supp : ∀ σ, magSumS σ ≠ M → B.mulVec Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ_mem hσ
  have hΦ_supp : ∀ σ, magSumS σ ≠ M → Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΦ_mem hσ
  have hΨr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) (B.mulVec Φ)) =
        (μ : ℂ) • magSectorRestriction (M := M) (B.mulVec Φ) :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hΨ_eig hΨ_supp
  have hΦr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Φ) =
        (μ : ℂ) • magSectorRestriction (M := M) Φ :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH hΦ_supp
  have hφ_eig :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ := by
    have := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hΦr_eig
    have hre : (fun σ => (magSectorRestriction (M := M) Φ σ).re) = φ := by
      funext σ
      have hval : magSectorRestriction (M := M) Φ σ =
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ) := by
        rw [hΦdef]
        exact magSectorEmbedding_apply_subtype _ σ
      rw [hval, hφdef, Complex.ofReal_re]
    rwa [hre] at this
  have hφ_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * φ σ := by
    intro σ
    rw [hφdef]
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    have : (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) = v σ := by
      rw [← mul_assoc, hsq, one_mul]
    rw [this]; exact hv_pos σ
  have hΨr_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hΨr_eig
  have hΨr_im :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hΨr_eig
  obtain ⟨a, ha⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_of_irreducible A c hJ_real
      hIrred hφ_eig hφ_pos hΨr_re
  obtain ⟨b, hb⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_of_irreducible A c hJ_real
      hIrred hφ_eig hφ_pos hΨr_im
  refine ⟨⟨a, b⟩, ?_⟩
  funext ρ
  by_cases hρ : magSumS ρ = M
  · set σ : magConfigS V N M := ⟨ρ, hρ⟩ with hσdef
    have hre_eq : (B.mulVec Φ ρ).re = a * φ σ := by
      have := congrFun ha σ
      simpa [Pi.smul_apply, smul_eq_mul, magSectorRestriction, hσdef] using this
    have him_eq : (B.mulVec Φ ρ).im = b * φ σ := by
      have := congrFun hb σ
      simpa [Pi.smul_apply, smul_eq_mul, magSectorRestriction, hσdef] using this
    have hΦρ : Φ ρ = ((φ σ : ℝ) : ℂ) := by
      have hval : Φ σ.1 = (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ) := by
        rw [hΦdef]
        exact magSectorEmbedding_apply_subtype _ σ
      rw [hφdef]
      simpa [hσdef] using hval
    apply Complex.ext
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, hΦρ, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      rw [hre_eq]
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, hΦρ, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add]
      rw [him_eq]
  · rw [hΨ_supp ρ hρ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hΦ_supp ρ hρ, mul_zero]

/-- **PF GS Casimir eigenvector from a supplied irreducibility witness**.
Graph-agnostic variant of `tasaki23_pf_groundState_casimir_eigenvector`. -/
theorem tasaki23_pf_groundState_casimir_eigenvector_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    ∃ γ : ℂ,
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) :=
  tasaki23_pf_groundState_commuting_eigenvector_of_irreducible A c hJ_real hIrred
    (totalSpinSSquared V N)
    (heisenbergHamiltonianS_commute_totalSpinSSquared J N)
    (totalSpinSSquared_commute_totalSpinSOp3 (Λ := V) (N := N)).symm hv_pos hH

/-- **PF GS Casimir = predicted via witness, from a supplied irreducibility
witness**. Graph-agnostic variant of
`tasaki23_pf_groundState_casimir_eq_predicted_of_witness`. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_of_witness_of_irreducible
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hw_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨γ, hγ⟩ :=
    tasaki23_pf_groundState_casimir_eigenvector_of_irreducible A c hJ_real hIrred hv_pos hH
  have hγ_real : star γ = γ :=
    isHermitian_eigenvalue_star_eq (totalSpinSSquared_isHermitian V N) hγ
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
  have hpred_real :
      star ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hγ_eq : γ = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) :=
    tasaki23_marshallPositive_casimir_eigenvalue_eq A hv_pos hw_pos hγ_real hpred_real hγ hw_cas
  rw [← hγ_eq]
  exact hγ

/-- **PF GS Casimir = predicted at admissible sector, from a supplied
irreducibility witness**. Graph-agnostic variant of
`tasaki23_pf_groundState_casimir_eq_predicted_sector`. The predicted-Casimir
*witness* `w` still comes from the toy coupling (always complete-positive), so the
toy ingredient `tasaki23_toy_groundState_casimir_eq_predicted_at` is reused as-is. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_sector_of_irreducible
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨w, hw_pos, hw_cas⟩ :=
    tasaki23_toy_groundState_casimir_eq_predicted_at
      (N := N) (M := M) A c_toy horient hsB hM hc_strict_toy hA_ne hB_ne hN
  exact tasaki23_pf_groundState_casimir_eq_predicted_of_witness_of_irreducible
    (N := N) (M := M) A c hJ_real hIrred hv_pos hw_pos hH hw_cas

/-- **Per-sector lift + predicted Casimir from a supplied irreducibility
witness**. Graph-agnostic variant of `tasaki23_sector_lift_and_casimir`. -/
theorem tasaki23_sector_lift_and_casimir_of_irreducible
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
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
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal (J := J) N hJ_real hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding J
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  refine ⟨hH, ?_⟩
  exact tasaki23_pf_groundState_casimir_eq_predicted_sector_of_irreducible
    (N := N) (M := M) A c c_toy horient hsB hM hJ_real hc_strict_toy
    hA_ne hB_ne hN hIrred hv_pos hH


end LatticeSystem.Quantum
