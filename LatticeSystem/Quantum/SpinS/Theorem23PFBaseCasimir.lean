import LatticeSystem.Quantum.SpinS.Theorem23ToyWitnessPredicted
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted

/-!
# Base-sector predicted total Casimir for a general bipartite Heisenberg ground state

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3).

Tasaki's overlap step (§2.5, eq. 2.5.12) transfers the predicted total-Casimir value
from the *toy* Hamiltonian's ground state (the all-to-all bipartite coupling, whose
ground state sits exactly at the predicted total spin) to the ground state of an
*arbitrary* connected bipartite antiferromagnetic Heisenberg coupling `J`: both
ground states are Marshall positive, so their overlap is non-zero, and both are
total-Casimir eigenvectors, forcing their eigenvalues to coincide.

This module discharges the `hsource_cas` hypothesis of
`tasaki_2_5_theorem_2_3_sector_existence` /
`tasaki23_successor_sector_existence_with_lowered_predictedCasimir` at the base
extremal sector `M = min(|A|,|¬A|)·N`: the toy witness
`tasaki23_toy_groundState_casimir_eq_predicted` (#3711) supplies `hw_cas`, and the
overlap pin `tasaki23_pf_groundState_casimir_eq_predicted_of_witness` transfers the
predicted Casimir to the `J`-ground state.  The adjacent-sector ladder chain then
propagates the predicted value to the remaining sectors via `Ŝ⁻_tot`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42 (eq. 2.5.12).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Base-sector predicted total Casimir (overlap pin with the toy witness)** (for
`|¬A| ≤ |A|`): in the base extremal sector `M = min(|A|,|¬A|)·N`, the Marshall-positive
Perron–Frobenius ground state of an arbitrary connected bipartite antiferromagnetic
coupling `J` is a `(Ŝ_tot)²`-eigenvector at the predicted value
`tasaki23PredictedCasimirValue A N`.

The toy Hamiltonian's ground-state witness (#3711) supplies the predicted-Casimir
state in the same sector, and `tasaki23_pf_groundState_casimir_eq_predicted_of_witness`
transfers the value to the `J`-ground state.  This discharges the `hsource_cas`
hypothesis of the sector-existence chain at the base sector. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_base
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    [Nonempty (magConfigS V N
      (min (Finset.univ.filter (fun x : V => A x = true)).card
        (Finset.univ.filter (fun x : V => (! A x) = true)).card * N))]
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
    {μ : ℝ}
    {v : magConfigS V N
        (min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N) → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨w, hw_pos, hw_cas⟩ :=
    tasaki23_toy_groundState_casimir_eq_predicted A N c_toy horient hc_strict_toy
      h_intermediate
  exact tasaki23_pf_groundState_casimir_eq_predicted_of_witness A N c hJ_real hJ_pos
    hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hv_pos hw_pos hH hw_cas

end LatticeSystem.Quantum
