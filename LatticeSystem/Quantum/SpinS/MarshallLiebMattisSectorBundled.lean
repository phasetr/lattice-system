import LatticeSystem.Quantum.SpinS.Theorem23StructuralMagSectorPF
import LatticeSystem.Quantum.SpinS.Theorem23StructuralComplexSectorEigenvec
import LatticeSystem.Quantum.SpinS.Theorem23StructuralUniqueness
import LatticeSystem.Quantum.SpinS.MagConfig

/-!
# Bundled magnetization-sector Marshall–Lieb–Mattis ground-state theorems

Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), bundled ground-state forms on a
single magnetization sector — real-form and complex-form.

These bundle the canonical (`h_intermediate`-free) existence theorems
(`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`,
`exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector`)
with the canonical Marshall-positive uniqueness theorems
(`marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector`,
`marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector`)
into the forms most directly usable downstream.

They were previously stated in the base sector modules using the deprecated
`h_intermediate` hypothesis; this module relocates them above the `*Structural*`
canonical layer (so the base modules need not import their own canonical variants),
deriving the canonical hypotheses `hA_ne`/`hB_ne`/`hN` from `h_intermediate` via
`h_intermediate_imp_conditions` (`Nonempty V` is supplied as an instance argument).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.2, p. 41.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), ground-state form
on the magnetization sector**: for the bipartite antiferromagnetic
Heisenberg matrix restricted to the magnetization-`M` sector, there
exists a Marshall-positive ground-state eigenvector `sign · v` (with
`v > 0` componentwise) at some eigenvalue `μ < c`, AND any other
Marshall-positive eigenvector at the SAME eigenvalue `μ` is a positive
scalar multiple of it.

Bundles the canonical existence theorem
(`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`)
with the canonical same-eigenvalue uniqueness theorem
(`marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector`). -/
theorem marshallLiebMattis_spinS_heisenbergSector_groundState
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty V] [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧
      (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) ∧
      (∀ {w : magConfigS V N M → ℝ},
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w →
        (∀ σ, 0 < (marshallSignS A σ.1).re * w σ) →
        ∃ r : ℝ, 0 < r ∧
          w = r • (fun σ => (marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨hA_ne, hB_ne, hN⟩ := h_intermediate_imp_conditions A h_intermediate
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro w hw hw_pos
  have hsign_v_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * v σ) := fun σ => by
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  exact marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
    A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
    hmul hsign_v_pos hw hw_pos

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), strongest
ground-state form on the COMPLEX sector matrix**: bundles complex
existence with complex Marshall-positive uniqueness.  The COMPLEX-Hilbert-space
form of Tasaki §2.5 Theorem 2.2: the ground state of the un-dressed quantum
Heisenberg Hamiltonian restricted to the magnetization sector is unique (up to a
positive real scalar in its real part) and has the Marshall sign structure
`Φ σ := ((sign A σ.1).re * v σ : ℂ)` with `v > 0`. -/
theorem marshallLiebMattis_spinS_heisenbergSector_complexGroundState_full
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty V] [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) =
        (μ : ℂ) • (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) ∧
      (∀ {μ' : ℝ} {W : magConfigS V N M → ℂ},
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W = (μ' : ℂ) • W →
        (∀ σ, 0 < (marshallSignS A σ.1).re * (W σ).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ σ, (W σ).re = r * ((marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨hA_ne, hB_ne, hN⟩ := h_intermediate_imp_conditions A h_intermediate
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
      (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro μ' W hW hW_marshall_pos
  have hΦ_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ).re := fun σ => by
    change 0 < (marshallSignS A σ.1).re *
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector
      A c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN hmul hΦ_marshall_pos hW hW_marshall_pos
  refine ⟨hμ_eq.symm, r, hr_pos, fun σ => ?_⟩
  have hΦ_re : (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ).re =
      (marshallSignS A σ.1).re * v σ := by rw [Complex.ofReal_re]
  rw [hrel σ, hΦ_re]

end LatticeSystem.Quantum
