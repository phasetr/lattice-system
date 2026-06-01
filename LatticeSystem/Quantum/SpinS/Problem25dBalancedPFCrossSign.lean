import LatticeSystem.Quantum.SpinS.Problem25dBalancedPFSignCases

/-!
# Tasaki Problem 2.5.d: balanced Perron--Frobenius cross sign

This module extracts the concrete cross-sublattice negative sign conclusion
from the balanced Perron--Frobenius sign-case endpoint.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, solution pp. 498--499, equations
(S.22)--(S.23), and Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Balanced PF cross-sublattice sign endpoint -/

set_option linter.style.longLine false in
/-- Problem 2.5.d balanced Perron--Frobenius cross endpoint: for the concrete
balanced PF vector from the Theorem 2.3 / Theorem 2.4 endpoint, every
cross-sublattice pair has negative original two-spin correlation real part. -/
theorem twoSpinCorrelationS_re_neg_of_tasaki23_balanced_pf_cross
    (A : V → Bool) (x y : V) (hxy : x ≠ y) (hAxy : A x ≠ A y)
    (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
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
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      ∃ v0 : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) → ℝ,
        (∀ σ, 0 < v0 σ) ∧
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (v0 σ : ℂ))) ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun σ :
                magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
              marshallSignS A σ.1 * (v0 σ : ℂ))) =
          (μ : ℂ) •
            (magSectorEmbedding (fun σ :
                magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
              marshallSignS A σ.1 * (v0 σ : ℂ))) ∧
        finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ)) ≤ 1 ∧
        (twoSpinCorrelationS x y
          (magSectorEmbedding (fun σ :
              magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
            marshallSignS A σ.1 * (v0 σ : ℂ)))).re < 0 := by
  classical
  obtain ⟨μ, hmin_eq, v0, hv0_pos, hΦ_ne, hΦ_eig, huniq, hcases⟩ :=
    twoSpinCorrelationS_sign_cases_of_tasaki23_balanced_pf_cross
      A x y hxy hAxy N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn
      hJ_bipartite hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
  refine ⟨μ, hmin_eq, v0, hv0_pos, hΦ_ne, hΦ_eig, huniq, ?_⟩
  by_cases hxtrue : A x = true
  · have hyfalse : A y = false := by
      cases hy : A y
      · rfl
      exact (hAxy (by rw [hxtrue, hy])).elim
    exact hcases.2.2.1 hxtrue hyfalse
  · have hxfalse : A x = false := by
      cases hx : A x <;> simp [hx] at hxtrue ⊢
    have hytrue : A y = true := by
      cases hy : A y
      · exact (hAxy (by rw [hxfalse, hy])).elim
      · rfl
    exact hcases.2.2.2 hxfalse hytrue

end LatticeSystem.Quantum
