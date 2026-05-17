import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqAvgSubBiwNorm

/-!
# `⟨Néel⟩.re − min(...) = |Λ|·N/2 + ‖biw‖` unconditionally

biw-norm form of the existing `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`
identity. Combines PR #3051 (`⟨Néel⟩.re − avg = |Λ|·N/2`) with
PR #3126 (`min = avg − ‖biw‖`) via linarith:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min((pmA).re, (pm¬A).re) = |Λ|·N/2 + ‖biw‖`

unconditionally. Equivalent to `max(|A|, |¬A|)·N` since
`|Λ|·N/2 + ||A|−|¬A||·N/2 = (|Λ| + ||A|−|¬A||)·N/2 =
2·max(|A|, |¬A|)·N/2 = max(|A|, |¬A|)·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Néel⟩.re − min(...) = |Λ|·N/2 + ‖biw‖`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq_half_card_add_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have h1 := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
