import LatticeSystem.Quantum.SpinS.Theorem23PFSectorCasimir
import LatticeSystem.Quantum.SpinS.Theorem23StructuralToyGSPredictedCasimirAt
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFCasimirPredicted

/-!
# Structural PF GS Casimir = predicted at admissible sector (no `h_intermediate`)

(Thm23-#3887.11): structural variant of `tasaki23_pf_groundState_casimir_eq_predicted_sector`
using `tasaki23_toy_groundState_casimir_eq_predicted_at_structural` (Thm23-#3887.10) +
`tasaki23_pf_groundState_casimir_eq_predicted_of_witness_structural` (Thm23-#3887.8).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural PF GS Casimir = predicted at admissible sector (no `h_intermediate`)**. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_sector_structural
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
    tasaki23_toy_groundState_casimir_eq_predicted_at_structural
      (N := N) (M := M) A c_toy horient hsB hM hc_strict_toy hA_ne hB_ne hN
  exact tasaki23_pf_groundState_casimir_eq_predicted_of_witness_structural
    (N := N) (M := M) A c hJ_real hJ_pos
    hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hv_pos hw_pos hH hw_cas

end LatticeSystem.Quantum
