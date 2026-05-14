import LatticeSystem.Quantum.SpinS.NeelStateMagNormEqPredicted
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelBasisVecS

/-!
# Complement Néel-state magnetization norm = same predicted spin

PR #2857 proved
`‖magEigenvalueS (neelConfigOfS A N)‖ = ||A| − |¬A||·N/2`.

The complement-orientation Néel state has the negated
magnetization eigenvalue (PR from `magEigenvalueS_neelConfigOfS_complement_eq_neg`),
so its norm is the same:

  `‖magEigenvalueS (neelConfigOfS (¬A) N)‖ = ||A| − |¬A||·N/2`.

This is the orientation-independent total-spin magnitude of
Tasaki §2.5 Theorem 2.3.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

omit [DecidableEq Λ] in
/-- **Complement Néel-state magnetization norm = same predicted
total spin**:
`‖magEigenvalueS (neelConfigOfS (¬A) N)‖ = ||A| − |¬A||·N/2`. -/
theorem magEigenvalueS_neelConfigOfS_complement_norm_eq :
    ‖magEigenvalueS (neelConfigOfS (Λ := Λ) (fun x => ! A x) N)‖ =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        ((N : ℝ) / 2) := by
  rw [magEigenvalueS_neelConfigOfS_complement_eq_neg, norm_neg]
  exact magEigenvalueS_neelConfigOfS_norm_eq A N

end LatticeSystem.Quantum
