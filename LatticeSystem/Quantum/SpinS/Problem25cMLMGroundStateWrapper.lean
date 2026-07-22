import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapGroundStatePhase
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM

/-!
# Tasaki Problem 2.5.c: MLM ground-state wrapper

This module connects the Problem 2.5.c one-dimensional Heisenberg eigenspace
wrapper from `Problem25cAxisSwapGroundStatePhase` to the balanced
Marshall--Lieb--Mattis/SU(2) uniqueness endpoint.  Under the balanced
bipartite hypotheses and the Theorem 2.3 witness, the existing endpoint gives
`finrank <= 1` for the Heisenberg ground eigenspace at the Hermitian minimum.
The phase wrapper then proves that each squared single-site spin expectation is
`N(N+2)/12`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Problem 2.5.c balanced MLM ground-state wrapper: if the balanced Theorem 2.3
endpoint supplies one-dimensionality of the SU(2)-point Heisenberg ground
eigenspace, then any normalized non-zero vector at the Hermitian minimum has all
three squared single-site spin expectations equal to `N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_tasaki23_balanced_MLM_groundState
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ =
      (hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) : ℂ) • Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  obtain ⟨μ, hmin_eq, _hsectors_singleton, huniq⟩ :=
    exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder_t23_pf
      (V := V) A N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
  have hΦμ : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
    simpa [hmin_eq] using hΦ
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_zAxisRot_axisSwap_eigenphase
    (V := V) (N := N) J (μ : ℂ) x huniq hΦ_ne hΦnorm hΦμ

end LatticeSystem.Quantum
