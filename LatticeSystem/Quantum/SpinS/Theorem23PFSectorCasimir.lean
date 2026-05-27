import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimirAt
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted

/-!
# Per-sector predicted total Casimir for a general bipartite Heisenberg ground state

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) —
generalising the base-sector overlap pin `tasaki23_pf_groundState_casimir_eq_predicted_base`
(#3712) to **every** admissible sector.

Tasaki's overlap step (§2.5, eq. 2.5.12): in any admissible sector `M`, the toy
Hamiltonian's Marshall-positive ground state carries the predicted total Casimir
(#3730), so the Marshall-positive Perron–Frobenius ground state of an *arbitrary*
connected bipartite antiferromagnetic coupling `J` inherits it through the non-zero
Marshall overlap (`tasaki23_pf_groundState_casimir_eq_predicted_of_witness`).  This
discharges `hsource_cas` of the sector-existence chain at every admissible sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42 (eq. 2.5.12).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Per-sector predicted total Casimir (overlap pin with the per-sector toy witness)**
(for `|¬A| ≤ |A|`, non-degenerate `s_B > 0`): in every admissible sector
`M ∈ tasaki23GroundStateSectors A N`, the Marshall-positive Perron–Frobenius ground state
of an arbitrary connected bipartite antiferromagnetic coupling `J` is a `(Ŝ_tot)²`-
eigenvector at `tasaki23PredictedCasimirValue A N`. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_sector
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
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
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
    tasaki23_toy_groundState_casimir_eq_predicted_at A N c_toy horient hsB hM hc_strict_toy
      h_intermediate
  exact tasaki23_pf_groundState_casimir_eq_predicted_of_witness A N c hJ_real hJ_pos
    hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hv_pos hw_pos hH hw_cas

end LatticeSystem.Quantum
