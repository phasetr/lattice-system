import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Absolute value of `bipartiteImbalanceWeight`

PR #2825 established that `bipartiteImbalanceWeight A N` is a
real number lifted to `ℂ`:
`bipartiteImbalanceWeight A N = ((|A| − |¬A|)·N/2 : ℝ)`.

Its **absolute value** as a complex number is therefore the
absolute value of `(|A| − |¬A|)·N/2 : ℝ`, equivalently
`||A| − |¬A||·N/2`. This matches Tasaki §2.5 Theorem 2.3's
predicted total-spin value `||A| − |¬A||·S` (recall `S = N/2`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Norm of `bipartiteImbalanceWeight` (as a complex number)**:
`‖bipartiteImbalanceWeight A N‖ = ||A| − |¬A||·N/2`.

This is the `||A| − |¬A||·S` predicted total spin appearing in
Tasaki §2.5 Theorem 2.3 (recall `S = N/2`). -/
theorem bipartiteImbalanceWeight_norm_eq :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        ((N : ℝ) / 2) := by
  rw [bipartiteImbalanceWeight_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)]

end LatticeSystem.Quantum
