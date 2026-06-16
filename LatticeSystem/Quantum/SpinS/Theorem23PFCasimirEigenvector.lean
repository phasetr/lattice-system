import LatticeSystem.Math.PerronFrobeniusSimple
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFJointCasimir
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.Theorem23PFLadderLink

/-!
# Tasaki §2.5 Theorem 2.3 — the Perron ground state is a total-Casimir eigenvector

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  Step 1 of the total-spin
determination: the per-sector Marshall-positive Heisenberg ground state is a
joint eigenvector of the total Casimir `(Ŝtot)²`.

The mechanism is geometric simplicity of the Perron eigenvalue
(`PerronFrobenius.eigenvec_proportional_of_pos_eigenvec`): the shifted dressed
Heisenberg sector matrix is irreducible and non-negative, so its Perron
eigenspace is one-dimensional.  Since `[Ĥ, (Ŝtot)²] = 0`, applying `(Ŝtot)²`
to the ground state stays in that eigenspace, hence is a scalar multiple of
the ground state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobenius

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Geometric simplicity of the dressed sector Perron eigenvalue**: any real
eigenvector `w` of the shifted dressed Heisenberg sector matrix at the Perron
eigenvalue `r` (with strictly positive Perron eigenvector `v`) is a scalar
multiple of `v`.  Specialisation of
`PerronFrobenius.eigenvec_proportional_of_pos_eigenvec` to the irreducible
shifted dressed sector matrix. -/
@[deprecated "Use canonical (h_intermediate-free) variant" (since := "2026-05-30")]

theorem tasaki23_shiftedDressed_sector_eigenvec_proportional_legacy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {r : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = r • w) :
    ∃ s : ℝ, w = s • v :=
  eigenvec_proportional_of_pos_eigenvec
    (isIrreducible_shiftedDressedSReMatrixOnMagSector_legacy A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate)
    hv hv_pos hw

/-- **One-dimensionality of the Heisenberg sector ground eigenspace**: if `φ`
is a Marshall-positive eigenvector of the (un-dressed) Heisenberg sector matrix
at `μ` (i.e. `marshallSignS · φ > 0`), then every real eigenvector `w` of the
same sector matrix at the same `μ` is a scalar multiple of `φ`.

Marshall-conjugates `φ` and `w` to eigenvectors of the shifted dressed sector
matrix (where `marshallSignS · φ > 0` is the strictly positive Perron
eigenvector), applies the geometric simplicity
`tasaki23_shiftedDressed_sector_eigenvec_proportional_legacy`, and conjugates back. -/
@[deprecated "Use canonical (h_intermediate-free) variant" (since := "2026-05-30")]

theorem tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_legacy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
    tasaki23_shiftedDressed_sector_eigenvec_proportional_legacy A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hφs hφ_pos hws
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
    _ = s * (((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * φ σ) := by ring
    _ = s * φ σ := by rw [hsq, one_mul]

/-- **The per-sector Perron–Frobenius ground state is a total-Casimir
eigenvector**: the Marshall-positive Heisenberg sector ground state
`Φ = magSectorEmbedding (marshallSignS · v)` (`v > 0`, `Ĥ Φ = μ Φ`) satisfies
`(Ŝtot)² Φ = γ Φ` for some `γ : ℂ`.

Since `[Ĥ, (Ŝtot)²] = 0`, `(Ŝtot)² Φ` is a Heisenberg eigenvector at the same
`μ` supported in the same magnetization sector; its real and imaginary parts
are real Heisenberg sector eigenvectors at `μ`, each a scalar multiple of the
Marshall-positive ground state by the one-dimensionality
`tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_legacy`.  Recombining,
`(Ŝtot)² Φ = γ Φ`.  This pins the total spin of the ground state (total-spin
determination, Tasaki §2.5 p.42). -/
@[deprecated "Use canonical (h_intermediate-free) variant" (since := "2026-05-30")]

theorem tasaki23_pf_groundState_casimir_eigenvector_legacy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    ∃ γ : ℂ,
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  set Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hΦdef
  set φ : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * v σ with hφdef
  -- mem magSubspace m for Φ and Ψ := Casimir Φ
  have hΦ_mem :
      Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS _
  have hΨ_eig :
      (heisenbergHamiltonianS J N).mulVec ((totalSpinSSquared V N).mulVec Φ) =
        (μ : ℂ) • (totalSpinSSquared V N).mulVec Φ :=
    mulVec_preserves_eigenvalue_of_commuteS
      (heisenbergHamiltonianS_commute_totalSpinSSquared J N) hH
  have hΨ_mem :
      (totalSpinSSquared V N).mulVec Φ ∈
        magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    rw [mem_magSubspaceS_iff] at hΦ_mem ⊢
    exact mulVec_preserves_eigenvalue_of_commuteS
      (totalSpinSSquared_commute_totalSpinSOp3 (Λ := V) (N := N)).symm hΦ_mem
  -- complex sector restrictions
  have hΨ_supp : ∀ σ, magSumS σ ≠ M → (totalSpinSSquared V N).mulVec Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ_mem hσ
  have hΦ_supp : ∀ σ, magSumS σ ≠ M → Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΦ_mem hσ
  have hΨr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) ((totalSpinSSquared V N).mulVec Φ)) =
        (μ : ℂ) • magSectorRestriction (M := M) ((totalSpinSSquared V N).mulVec Φ) :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hΨ_eig hΨ_supp
  have hΦr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Φ) =
        (μ : ℂ) • magSectorRestriction (M := M) Φ :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH hΦ_supp
  -- φ is the Marshall-positive real Heisenberg sector eigenvector at μ
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
  -- re / im parts of Ψ_r are heis sector eigenvectors at μ
  have hΨr_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hΨr_eig
  have hΨr_im :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
      N hJ_real hΨr_eig
  -- one-dimensionality ⟹ re, im parts are scalar multiples of φ
  obtain ⟨a, ha⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_legacy A N c hJ_real
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hφ_eig hφ_pos hΨr_re
  obtain ⟨b, hb⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_legacy A N c hJ_real
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hφ_eig hφ_pos hΨr_im
  -- assemble γ = a + b i
  refine ⟨⟨a, b⟩, ?_⟩
  funext ρ
  by_cases hρ : magSumS ρ = M
  · -- ρ is in the sector: use re/im relations at σ = ⟨ρ, hρ⟩
    set σ : magConfigS V N M := ⟨ρ, hρ⟩ with hσdef
    have hre_eq : ((totalSpinSSquared V N).mulVec Φ ρ).re = a * φ σ := by
      have := congrFun ha σ
      simpa [Pi.smul_apply, smul_eq_mul, magSectorRestriction, hσdef] using this
    have him_eq : ((totalSpinSSquared V N).mulVec Φ ρ).im = b * φ σ := by
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
  · -- outside the sector both sides vanish
    rw [hΨ_supp ρ hρ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hΦ_supp ρ hρ, mul_zero]

/-- **Adjacent-sector ladder link for the Perron ground state from
Casimir non-vanishing**: the per-sector Marshall-positive Heisenberg ground
state `Φ = magSectorEmbedding (marshallSignS · v)` (`v > 0`, `Ĥ Φ = μ Φ`)
satisfies the adjacent-sector ladder link as soon as its (automatically
existing) total-Casimir eigenvalue is away from the lowering-kernel value:
`Ŝ⁻_tot · Φ` is a non-zero Heisenberg eigenvector at the same `μ` in the next
magnetization sector.

This replaces the predicted-GS-membership hypothesis of
`tasaki23_pf_ladder_link_succ_of_mem_predictedGS` by the minimal
Casimir-non-vanishing condition, using that the ground state is a
total-Casimir eigenvector (`tasaki23_pf_groundState_casimir_eigenvector_legacy`).
It is the form in which the sound chain applies directly to the actual
Perron–Frobenius ground state. -/
theorem tasaki23_pf_groundState_ladder_link_of_casimir_ne_kernel
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty V] [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hγ_ne : ∀ γ : ℂ,
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) →
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1))) :
    (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) =
        (μ : ℂ) • (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ≠ 0 ∧
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) := by
  obtain ⟨hA_ne, hB_ne, hN⟩ := h_intermediate_imp_conditions A h_intermediate
  obtain ⟨γ, hγ⟩ :=
    tasaki23_pf_groundState_casimir_eigenvector A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hv_pos hH
  exact tasaki23_pf_ladder_link_succ hH hγ (hγ_ne γ hγ)
    (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)

end LatticeSystem.Quantum
