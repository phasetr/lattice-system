import LatticeSystem.Quantum.SpinS.NeelToyEnergyGapEqZeroIffSaturated

/-!
# Néel expectation = predictedSymm iff saturated edge at `N ≥ 1`

PR (existing) `neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_eq_zero_iff_saturated`
gave the gap iff:

  `(⟨Néel⟩ − predictedSymm).re = 0 ↔ |A| = 0 ∨ |¬A| = 0` at `N ≥ 1`.

This file packages the **direct equality iff**:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re = (predictedSymm A).re
    ↔ |A| = 0 ∨ |¬A| = 0` at `N ≥ 1`.

The Néel state attains the symmetric Tasaki §2.5 Theorem 2.3
prediction exactly at saturated edge — the only configuration where
the Néel state itself is the predicted ground state.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩ = predictedSymm iff saturated edge at `N ≥ 1`**. Direct
equality form of the existing gap-iff theorem. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_predictedSymm_re_iff_saturated
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  have hgap_iff :=
    neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_eq_zero_iff_saturated
      (Λ := Λ) A hN
  -- (⟨Néel⟩ − predictedSymm).re = ⟨Néel⟩.re − predictedSymm.re.
  rw [Complex.sub_re] at hgap_iff
  -- ⟨Néel⟩.re − predictedSymm.re = 0 ↔ ⟨Néel⟩.re = predictedSymm.re.
  rw [sub_eq_zero] at hgap_iff
  exact hgap_iff

end LatticeSystem.Quantum
