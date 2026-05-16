import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# Néel expectation vs orientation-pair max: gap = `min(|A|, |¬A|)·N`

PR #3001: `max((pmA).re, (pm¬A).re) = predictedSymm.re`.
Existing: `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩ − predictedSymm = min(|A|, |¬A|)·N`
(`neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm`).

Composing:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max((pmA).re, (pm¬A).re) = min(|A|, |¬A|)·N`

unconditionally. This closes the operator–algebraic affine triangle:
- Néel − min   = max(|A|, |¬A|)·N
- Néel − avg   = |Λ|·N/2
- Néel − max   = min(|A|, |¬A|)·N (this PR)
- Néel − predictedSymm = min(|A|, |¬A|)·N (existing; equals Néel − max
  since `max = predictedSymm`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel expectation sits `min(|A|, |¬A|)·N` above the orientation-pair max**:

  `⟨Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)⟩.re − max(...) = min(|A|, |¬A|)·N`

unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) (A := A) (N := N)
  have hre := congrArg Complex.re hgap
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero] at hre
  rw [hre]
  push_cast [Nat.cast_min]
  ring

end LatticeSystem.Quantum
