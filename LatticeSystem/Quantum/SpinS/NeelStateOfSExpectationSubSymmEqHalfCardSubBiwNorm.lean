import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgEqSymmSubBiwNorm

/-!
# `⟨Néel⟩.re − predictedSymm.re = |Λ|·N/2 − ‖biw‖` unconditionally

biw-norm form of the existing `⟨Néel⟩.re − predictedSymm.re =
min(|A|, |¬A|)·N` identity:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − predictedSymm.re = |Λ|·N/2 − ‖biw‖`

unconditionally, where `‖biw‖ = ||A|−|¬A||·N/2`. Combines PR #3051
(`⟨Néel⟩.re − avg = |Λ|·N/2`) with PR #3123 (`avg = predictedSymm − ‖biw‖`)
via linarith.

Equivalent to `min(|A|, |¬A|)·N` because
`|Λ|·N/2 − ||A|−|¬A||·N/2 = (|Λ| − ||A|−|¬A||)·N/2 = 2·min(|A|, |¬A|)·N/2
 = min(|A|, |¬A|)·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Néel⟩.re − predictedSymm.re = |Λ|·N/2 − ‖biw‖`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_predictedSymm_re_eq_half_card_sub_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have h1 := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_avg_complement_re_eq_predictedSymm_re_sub_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
