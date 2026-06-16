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
total-Casimir eigenvector (`tasaki23_pf_groundState_casimir_eigenvector`).
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
