import LatticeSystem.Quantum.SpinS.Problem25cMLMGroundStateWrapper

/-!
# Tasaki Problem 2.5.c: balanced structural wrapper

This module removes the explicit Theorem 2.3 witness from the balanced
Problem 2.5.c MLM ground-state wrapper.  The structural Theorem 2.3 closure
supplies that witness directly from the standard balanced bipartite
antiferromagnetic hypotheses.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Problem 2.5.c balanced structural wrapper: in the balanced bipartite
antiferromagnetic case, the structural Theorem 2.3 proof supplies the MLM/SU(2)
uniqueness endpoint, so every normalized non-zero Heisenberg ground-state
eigenvector has all three squared single-site spin expectations equal to
`N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_balanced_bipartiteCompletePositive
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
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
  classical
  have horient :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card := by
    rw [← h_card_eq]
  have hsB :
      0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
        (N : ℝ) / 2 := by
    have hB_pos :
        0 < (Finset.univ.filter (fun x : V => (! A x) = true)).card :=
      lt_of_lt_of_le Nat.zero_lt_one hcardB
    have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    have hB_pos_real :
        0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hB_pos
    have hN_pos_real : 0 < (N : ℝ) := by
      exact_mod_cast hN_pos
    nlinarith
  have hT23 : tasaki_2_5_theorem_2_3 A N J c :=
    tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive
      (V := V) (J := J) A N c c_toy horient hsB hc_strict_toy
  exact
    singleSiteSpinSquareExpectationS_all_axes_eq_of_tasaki23_balanced_MLM_groundState
      (V := V) A N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB x hΦ_ne hΦnorm hΦ

end LatticeSystem.Quantum
