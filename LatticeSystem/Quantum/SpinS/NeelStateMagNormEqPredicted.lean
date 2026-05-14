import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# Néel-state magnetization norm = Tasaki §2.5 Theorem 2.3 predicted spin

The Néel-state magnetization eigenvalue equals the signed
bipartite imbalance weight (PR #2773):

  `magEigenvalueS (neelConfigOfS A N) = bipartiteImbalanceWeight A N`.

Its norm therefore equals the Tasaki §2.5 Theorem 2.3 predicted
total spin magnitude `||A| − |¬A||·N/2 = ||A| − |¬A||·S`:

  `‖magEigenvalueS (neelConfigOfS A N)‖ = ||A| − |¬A||·N/2`.

This is the direct quantitative bridge from the variational
input (Néel state) to the predicted-spin output of Theorem 2.3.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

omit [DecidableEq Λ] in
/-- **Néel-state magnetization norm = predicted Theorem 2.3 spin**:
`‖magEigenvalueS (neelConfigOfS A N)‖ = ||A| − |¬A||·N/2`. -/
theorem magEigenvalueS_neelConfigOfS_norm_eq :
    ‖magEigenvalueS (neelConfigOfS (Λ := Λ) A N)‖ =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        ((N : ℝ) / 2) := by
  rw [magEigenvalueS_neelConfigOfS_eq_bipartiteImbalanceWeight]
  exact bipartiteImbalanceWeight_norm_eq A N

end LatticeSystem.Quantum
