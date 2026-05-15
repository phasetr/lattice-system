import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap

/-!
# Strict positive Néel-to-predicted-min energy gap at non-degenerate

PR #2884 established the (complex) equality

  `<Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)>
     − bipartiteToyMinEnergyPredictedSymm A N
     = min(|A|, |¬A|) · N`.

In the **non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`),
the gap real part is **strictly positive**:

  `0 < (<Φ_Néel|Ĥ|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm).re`,

since `min(|A|, |¬A|) · N > 0` strictly under non-degeneracy.

This shows the Néel state is **strictly above** the symmetric
predicted minimum at non-degenerate configurations.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict positivity of the Néel-vs-predicted-min energy gap**
in the non-degenerate case. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_pos_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    0 < (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N)) -
          bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm]
  -- (min(|A|, |¬A|) · N : ℂ).re = min(|A|, |¬A|) · N > 0.
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Nat.cast_min]
  have hA_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have hAc_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmin_pos :
      0 < min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    lt_min hA_pos hAc_pos
  nlinarith [hmin_pos, hN_pos]

end LatticeSystem.Quantum
