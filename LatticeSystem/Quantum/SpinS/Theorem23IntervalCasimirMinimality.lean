import LatticeSystem.Quantum.SpinS.Theorem23IntervalCasimir

/-!
# Tasaki §2.5 Theorem 2.3 interval-Casimir minimality suffix

This module contains the global / sector minimality bridges and named callback
definitions split from `Theorem23IntervalCasimir.lean`. The base
interval-Casimir module keeps the predicted-Casimir interval-chain wrappers,
while this suffix exposes the final minimality bridge and callback API consumed
by the outside-ground and final-boundary modules.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 global-minimality bridge from sectors**:
to prove the full-Hilbert-space global minimality clause, it is enough to
prove the same lower bound in every magnetization sector.

Given a nonzero full-space eigenvector, choose a configuration where it is
nonzero, restrict to that configuration's `magSumS` sector, and use the
sector-restriction eigenvector bridge. This reduces the remaining global
minimality input for Theorem 2.3 to a sectorwise statement. -/
theorem tasaki23_global_minimality_of_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hsector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
          Φ ≠ 0 →
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
            (μ' : ℂ) • Φ →
          μ ≤ μ') :
    ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ' := by
  intro μ' Ψ' hΨ'_ne hΨ'_eigen
  classical
  have hnonzero_point : ∃ σ : V → Fin (N + 1), Ψ' σ ≠ 0 := by
    by_contra h
    apply hΨ'_ne
    funext σ
    by_contra hσ
    exact h ⟨σ, hσ⟩
  obtain ⟨σ, hσ_ne⟩ := hnonzero_point
  let M : ℕ := magSumS σ
  letI : Nonempty (magConfigS V N M) := ⟨⟨σ, rfl⟩⟩
  have hrestr_ne :
      magSectorRestriction (M := M) Ψ' ≠ 0 := by
    intro hzero
    have hval := congrFun hzero ⟨σ, rfl⟩
    exact hσ_ne hval
  have hrestr_eigen :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Ψ') =
        (μ' : ℂ) • magSectorRestriction (M := M) Ψ' :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J hΨ'_eigen
  exact hsector_min M hrestr_ne hrestr_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-minimality bridge from real sectors**:
for real coupling, it is enough to prove the sector lower bound for
nonzero real-form sector eigenvectors.

An arbitrary nonzero complex sector eigenvector has either nonzero real
part or nonzero imaginary part.  Since the complex sector matrix has real
entries under `hJ_real`, that nonzero component is an eigenvector of the
real-form sector matrix at the same real eigenvalue. -/
theorem tasaki23_sector_minimality_of_real_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hreal_sector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ') :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  intro M _ μ' Φ hΦ_ne hΦ_eigen
  classical
  by_cases hRe_ne : (fun σ : magConfigS V N M => (Φ σ).re) ≠ 0
  · exact hreal_sector_min M hRe_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦ_eigen)
  · have hRe_zero : (fun σ : magConfigS V N M => (Φ σ).re) = 0 := by
      by_contra h
      exact hRe_ne h
    have hIm_ne : (fun σ : magConfigS V N M => (Φ σ).im) ≠ 0 := by
      intro hIm_zero
      apply hΦ_ne
      funext σ
      apply Complex.ext
      · have h := congrFun hRe_zero σ
        simpa using h
      · have h := congrFun hIm_zero σ
        simpa using h
    exact hreal_sector_min M hIm_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        N hJ_real hΦ_eigen)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain callback**:
the adjacent-sector chain has produced one real energy `μ` realised by a
strictly positive Marshall representative in every admissible
`tasaki23GroundStateSectors` sector.

This names the central interval-chain output used by the final global
minimality wrappers. -/
def tasaki23CommonEnergyChain
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c μ : ℝ) : Prop :=
  ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
    ∃ v : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-minimality callback**:
after the common-energy chain has selected `μ`, this callback states that
`μ` is a lower bound for every nonzero complex eigenvector in every
magnetization sector.

This names the sectorwise global-minimality input used by the direct
lowered-site-sum final wrappers. -/
def tasaki23SectorMinimalityCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ {μ : ℝ},
    tasaki23CommonEnergyChain (V := V) A J N c μ →
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
          Φ ≠ 0 →
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
            (μ' : ℂ) • Φ →
          μ ≤ μ'


end LatticeSystem.Quantum
