import LatticeSystem.Quantum.SpinS.Problem25dBalancedPFEndpoint

/-!
# Tasaki Problem 2.5.d: balanced Perron--Frobenius sign cases

This module applies the final bipartite-gauge sign conversion to the concrete
balanced Perron--Frobenius endpoint from `Problem25dBalancedPFEndpoint`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, solution pp. 498--499, equations
(S.22)--(S.23), and Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Balanced PF sign endpoint -/

/-- Problem 2.5.d balanced Perron--Frobenius sign endpoint: the concrete
balanced PF vector from the Theorem 2.3 / Theorem 2.4 endpoint satisfies the
original two-spin correlation sign cases after bipartite-gauge conversion. -/
theorem twoSpinCorrelationS_sign_cases_of_tasaki23_balanced_pf_cross
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
        ((A x = true → A y = true →
            0 < (twoSpinCorrelationS x y
              (magSectorEmbedding (fun σ :
                  magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
                marshallSignS A σ.1 * (v0 σ : ℂ)))).re) ∧
          (A x = false → A y = false →
            0 < (twoSpinCorrelationS x y
              (magSectorEmbedding (fun σ :
                  magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
                marshallSignS A σ.1 * (v0 σ : ℂ)))).re) ∧
          (A x = true → A y = false →
            (twoSpinCorrelationS x y
              (magSectorEmbedding (fun σ :
                  magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
                marshallSignS A σ.1 * (v0 σ : ℂ)))).re < 0) ∧
          (A x = false → A y = true →
            (twoSpinCorrelationS x y
              (magSectorEmbedding (fun σ :
                  magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
                marshallSignS A σ.1 * (v0 σ : ℂ)))).re < 0)) := by
  classical
  obtain ⟨μ, hmin_eq, v0, hv0_pos, hΦ_ne, hΦ_eig, huniq, hpos⟩ :=
    twoSpinCorrelationS_bipartite_signed_re_pos_of_tasaki23_balanced_pf_cross
      A hxy hAxy N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
  refine ⟨μ, hmin_eq, v0, hv0_pos, hΦ_ne, hΦ_eig, huniq, ?_⟩
  exact twoSpinCorrelationS_sign_cases_of_bipartite_signed_re_pos A x y hpos

end LatticeSystem.Quantum
