import LatticeSystem.Math.FiniteStrictUpperBound
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem23StructuralFullHilbertEigenvec
import LatticeSystem.Quantum.SpinS.Theorem23StructuralUniqueness

/-!
# Structural Tasaki §2.5 Theorem 2.2 bundled full-Hilbert form (no `h_intermediate`)

(Thm23-#3887.15): structural variant of
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full_legacy` bundling
- existence (Thm23-#3887.13 `exists_marshallSign_eigenvector_heisenbergHamiltonianS_full`)
- support (zero outside sector — direct from `magSectorEmbedding_apply_of_not_mem`)
- uniqueness (Thm23-#3887.14
  `marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector`)
into the textbook statement of the §2.5 Theorem 2.2 ground state on the actual quantum
Heisenberg Hamiltonian, with `(hA_ne, hB_ne, hN)` instead of `h_intermediate`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.2, pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural Tasaki §2.5 Theorem 2.2 bundled (no `h_intermediate`)**.

The diagonal shift of the Perron–Frobenius step (Tasaki's own `α` in the proof of Theorem A.18,
p. 475, step (1)) is produced internally by `LatticeSystem.Math.exists_gt_of_finite` rather than
assumed, so no auxiliary spectral parameter appears in the statement; the comparison against such
a shift is available separately as
`marshallSign_sector_eigenvalue_lt_of_dressedDiagonal_lt`.

The statement is per-sector: it fixes a magnetization index `M`, and its uniqueness clause ranges
over competitors that are both supported on that sector and Marshall-positive. It therefore does
not assert that `μ` is the minimum of the whole spectrum, nor anything about the total spin. -/
theorem marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    (A : V → Bool)
    {J : V → V → ℂ} {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (∀ σ, 0 < v σ) ∧
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
  obtain ⟨c, hc_strict⟩ := LatticeSystem.Math.exists_gt_of_finite
    (fun σ : V → Fin (N + 1) => dressedHeisenbergSReMatrix A J N σ σ)
  obtain ⟨μ, v, _hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianS_full
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  refine ⟨μ, v, hv_pos, hmul, ?_, ?_⟩
  · intro σ hne
    exact magSectorEmbedding_apply_of_not_mem _ hne
  · intro μ' Ψ' hΨ' hΨ'_supp hΨ'_marshall_pos
    have hΨ'_sec :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction
        J hΨ' hΨ'_supp
    have hsec_ground :
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) =
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
      marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector
        (N := N) (M := M) A c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        hA_ne hB_ne hN hsec_ground (by
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

/-- **The Marshall-positive sector eigenvalue lies below any strict bound on the dressed
diagonal.** This is the opt-in form of the comparison that
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full` no longer carries as a
conjunct: a caller that has its own shift `c` above every dressed diagonal entry recovers
`μ < c` for the Marshall-positive sector eigenvector it obtained, without that shift having to
appear in the bundled statement.  Both eigenvalues are pinned to the same sector value by the
bundled theorem's uniqueness clause, so no new spectral input is used. -/
theorem marshallSign_sector_eigenvalue_lt_of_dressedDiagonal_lt
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
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hmul : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    μ < c := by
  have hpos : ∀ (w : magConfigS V N M → ℝ), (∀ σ, 0 < w σ) →
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (magSectorEmbedding
            (fun τ' => (((marshallSignS A τ'.1).re * w τ' : ℝ) : ℂ)) τ.1).re := by
    intro w hw τ
    rw [magSectorEmbedding_apply_subtype, Complex.ofReal_re]
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hw τ
  obtain ⟨μ₀, v₀, _hv₀_pos, _hmul₀, _hsupp₀, huniq₀⟩ :=
    marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
      (N := N) (M := M) A hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hA_ne hB_ne hN
  obtain ⟨μ₁, v₁, hμ₁_lt, hv₁_pos, hmul₁⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianS_full
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  have h₀ : μ = μ₀ :=
    (huniq₀ hmul (fun σ hne => magSectorEmbedding_apply_of_not_mem _ hne)
      (hpos v hv_pos)).1
  have h₁ : μ₁ = μ₀ :=
    (huniq₀ hmul₁ (fun σ hne => magSectorEmbedding_apply_of_not_mem _ hne)
      (hpos v₁ hv₁_pos)).1
  linarith

end LatticeSystem.Quantum
