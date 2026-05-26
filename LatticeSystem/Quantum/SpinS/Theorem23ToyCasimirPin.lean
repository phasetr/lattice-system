import LatticeSystem.Quantum.SpinS.CasimirSpectralLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

/-!
# Pinning the toy ground state's total Casimir to the predicted value

Issue #3674 (the abstract variational lower bound completing the toy-ground-state
predicted-Casimir witness; Issue #3658 PR 4 / #3542).

In the **extremal magnetization sector** `m = S_tot = |s_A − s_B|`, the total
Casimir of a joint Casimir eigenvector is pinned to the predicted value by a
two-sided squeeze:

* lower bound `γ_tot.re ≥ m(m+1) = predicted` — the magnetization lower bound
  (`totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS`), since the total spin
  dominates its `z`-projection `m`;
* upper bound `γ_tot.re ≤ predicted` — from the toy energy formula
  `μ = γ_tot − γ_A − γ_B`, the sublattice Casimir max bounds `γ_A ≤ s_A(s_A+1)`,
  `γ_B ≤ s_B(s_B+1)`, and the reference energy bound `μ ≤ predicted − s_A(s_A+1) −
  s_B(s_B+1)`.

This pin isolates the two remaining obligations as hypotheses: the extremal-sector
magnetization (`hM`) and the reference energy bound (`hμ`, from a Marshall-positive
member of the predicted joint eigenspace).  No Clebsch–Gordan triangle inequality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- The predicted total spin `|s_A − s_B|` is non-negative. -/
theorem tasaki23PredictedTotalSpin_nonneg (A : V → Bool) :
    0 ≤ tasaki23PredictedTotalSpin (V := V) A N := by
  rw [tasaki23PredictedTotalSpin]
  positivity

/-- **Toy total-Casimir pin (extremal sector)**: a non-zero `(Ŝ_tot)²`-eigenvector
`v` at `γ_tot` lying in the magnetization subspace at the predicted total spin
`M.re = |s_A − s_B|`, that is also a `(Ŝ_A)²` / `(Ŝ_¬A)²` joint eigenvector with
`γ_A.re ≤ s_A(s_A+1)`, `γ_B.re ≤ s_B(s_B+1)` and toy energy bounded by the
reference `(γ_tot − γ_A − γ_B).re ≤ predicted − s_A(s_A+1) − s_B(s_B+1)`, has
`γ_tot.re = predicted`. -/
theorem tasaki23_total_casimir_re_eq_predicted_of_bounds (A : V → Bool)
    {γ_tot γ_A γ_B M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hv_mem : v ∈ magSubspaceS V N M)
    (hM : M.re = tasaki23PredictedTotalSpin (V := V) A N)
    (htot : (totalSpinSSquared V N).mulVec v = γ_tot • v)
    (hA_le : γ_A.re ≤
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1))
    (hB_le : γ_B.re ≤
      ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1))
    (hμ : (γ_tot - γ_A - γ_B).re ≤
      tasaki23PredictedCasimirValue (V := V) A N -
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) :
    γ_tot.re = tasaki23PredictedCasimirValue (V := V) A N := by
  -- Lower bound: predicted = M.re (M.re + 1) ≤ γ_tot.re.
  have hM_nn : 0 ≤ M.re := by rw [hM]; exact tasaki23PredictedTotalSpin_nonneg A
  have hlow : M.re * (M.re + 1) ≤ γ_tot.re :=
    totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS hv hv_mem hM_nn htot
  have hpred : tasaki23PredictedCasimirValue (V := V) A N = M.re * (M.re + 1) := by
    rw [tasaki23PredictedCasimirValue, hM]
  -- Upper bound: γ_tot.re = (γ_tot − γ_A − γ_B).re + γ_A.re + γ_B.re ≤ predicted.
  have hsub : (γ_tot - γ_A - γ_B).re = γ_tot.re - γ_A.re - γ_B.re := by
    rw [Complex.sub_re, Complex.sub_re]
  rw [hsub] at hμ
  rw [hpred] at hμ ⊢
  linarith

end LatticeSystem.Quantum
