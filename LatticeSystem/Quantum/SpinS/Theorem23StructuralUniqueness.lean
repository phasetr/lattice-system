import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.Theorem23StructuralReach

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Structural Marshall-positive sector eigenvector uniqueness (no `h_intermediate`)

(Thm23-#3887.14): structural variants of the Marshall-positive sector eigenvector
uniqueness chain, swapping `pos_eigenvec_unique` at the bottom from the
`h_intermediate`-dependent irreducibility to the structural irreducibility
`isIrreducible_shiftedDressedSReMatrixOnMagSector_structural` (Thm23-#3887.1).

Provides four wrappers (bottom-up):
- `pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector_structural`
- `pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector_structural`
- `marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector_structural`
- `marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector_structural`

The eigenvalue-uniqueness side (`pos_eigenvec_eigenvalue_unique_*`,
`marshallPositive_eigenvec_eigenvalue_unique_*`) already does NOT use `h_intermediate`,
so we reuse those directly.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.2, pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural shifted-dressed PF positive eigenvector uniqueness (no `h_intermediate`)**. -/
theorem pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector_structural
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  LatticeSystem.Math.PerronFrobenius.pos_eigenvec_unique
    (isIrreducible_shiftedDressedSReMatrixOnMagSector_structural (N := N) (M := M)
      A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN)
    hv hv_pos hw hw_pos

/-- **Structural dressed Heisenberg PF positive eigenvector uniqueness (no `h_intermediate`)**. -/
theorem pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector_structural
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v := by
  have hv' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hv
  have hw' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hw
  exact pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector_structural
    (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    hA_ne hB_ne hN hv' hv_pos hw' hw_pos

/-- **Structural Marshall-positive Heisenberg sector eigenvector uniqueness
(no `h_intermediate`)**. -/
theorem marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector_structural
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    ∃ r : ℝ, 0 < r ∧ w₂ = r • w₁ := by
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₂
  obtain ⟨r, hr_pos, hrel⟩ :=
    pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector_structural
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos
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

/-- **Structural Marshall-positive complex sector eigenvector uniqueness
(no `h_intermediate`)**. -/
theorem marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector_structural
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ₁ μ₂ : ℝ} {W₁ W₂ : magConfigS V N M → ℂ}
    (hW₁ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₁ =
      (μ₁ : ℂ) • W₁)
    (hW₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₁ σ).re)
    (hW₂ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₂ =
      (μ₂ : ℂ) • W₂)
    (hW₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₂ σ).re) :
    μ₁ = μ₂ ∧ ∃ r : ℝ, 0 < r ∧
      ∀ σ, (W₂ σ).re = r * (W₁ σ).re := by
  have hW₁_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hW₁
  have hW₂_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hW₂
  have hμ_eq : μ₁ = μ₂ :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  refine ⟨hμ_eq, ?_⟩
  subst hμ_eq
  obtain ⟨r, hr_pos, hrel⟩ :=
    marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector_structural
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  exact ⟨r, hr_pos, fun σ => congrFun hrel σ⟩

end LatticeSystem.Quantum
