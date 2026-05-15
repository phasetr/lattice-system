import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap

/-!
# Néel-vs-predicted-min gap real part `≥ N` at non-degenerate

PR #2884 established the gap equality
`<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N
   = min(|A|, |¬A|) · N` (as complex numbers).

In the **non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`), we have
`min(|A|, |¬A|) ≥ 1`, hence the gap real part satisfies the
quantitative lower bound

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N).re
     ≥ N`.

A strictly-quantitative refinement of PR #2893's strict positivity.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Quantitative Néel-vs-predictedSymm gap lower bound**:
at `|A| ≥ 1` and `|¬A| ≥ 1`,
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N).re
   ≥ N`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_ge_N_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (N : ℝ) ≤
      (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N)) -
          bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Nat.cast_min]
  have hA_pos : (1 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    exact_mod_cast hA
  have hAc_pos : (1 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hAc
  have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmin_ge_one :
      (1 : ℝ) ≤
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    le_min hA_pos hAc_pos
  nlinarith [hmin_ge_one, hN_nn]

end LatticeSystem.Quantum
