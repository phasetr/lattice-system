import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqAvgAddBiwNorm

/-!
# `⟨Néel⟩.re − max(...) = |Λ|·N/2 − ‖biw‖` unconditionally

Mirror of PR #3174. biw-norm form of the existing `⟨Néel⟩.re − max(...) =
min(|A|, |¬A|)·N` identity. Combines PR #3051 (`⟨Néel⟩.re − avg = |Λ|·N/2`)
with PR #3125 (`max = avg + ‖biw‖`) via linarith:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max((pmA).re, (pm¬A).re) = |Λ|·N/2 − ‖biw‖`

unconditionally. Equivalent to `min(|A|, |¬A|)·N` since
`|Λ|·N/2 − ||A|−|¬A||·N/2 = min(|A|, |¬A|)·N`.

Also matches PR #3173 (`⟨Néel⟩.re − predictedSymm.re = |Λ|·N/2 − ‖biw‖`)
via PR #3001 (`max = predictedSymm.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Néel⟩.re − max(...) = |Λ|·N/2 − ‖biw‖`** unconditionally. Mirror of PR #3174. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq_half_card_sub_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have h1 := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
