import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFSectorCasimir
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall

/-!
# Structural per-sector lift + predicted Casimir (no `h_intermediate`)

(PR #3893): structural variant of `tasaki23_sector_lift_and_casimir_legacy`
(in `Theorem23IntervalCommonEnergy.lean`) using
`tasaki23_pf_groundState_casimir_eq_predicted_sector` (Thm23-#3887.11).

Lifts a Marshall-positive real sector eigenvector to the full Hilbert space
(`heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal` +
`heisenbergHamiltonianS_mulVec_magSectorEmbedding`) and identifies its
total Casimir as the predicted value, with `(hA_ne, hB_ne, hN)` instead of the
vacuous-at-N=1 `h_intermediate`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural per-sector lift + predicted Casimir (no `h_intermediate`)**. -/
theorem tasaki23_sector_lift_and_casimir
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
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
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal (J := J) N hJ_real
    hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding J
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  refine ⟨hH, ?_⟩
  exact tasaki23_pf_groundState_casimir_eq_predicted_sector
    (N := N) (M := M) A c c_toy horient hsB hM
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
    hA_ne hB_ne hN hv_pos hH

end LatticeSystem.Quantum
