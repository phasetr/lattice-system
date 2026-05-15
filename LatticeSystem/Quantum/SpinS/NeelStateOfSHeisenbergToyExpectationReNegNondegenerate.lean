import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# Strict negativity of `<H_toy>_Néel.re` at non-degenerate

The Néel-state toy-Hamiltonian expectation closed form
(`neelStateOfS_heisenbergToyHamiltonianS_expectation`, γ-4 step 131)
is

  `<Φ_Néel|Ĥ_toy_S|Φ_Néel> = −|A|·|¬A|·N²/2`.

At **non-degenerate** (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`),
`|A|·|¬A|·N² > 0`, hence the real part is **strictly negative**:

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re < 0`.

This is the variational AFM-energy lower bound: any non-saturated
Néel-class candidate gives strictly negative toy-Hamiltonian
energy, consistent with the predicted GS energy
`bipartiteToyMinEnergyPredictedSymm < 0` (PR #2845).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict negativity of `<H_toy>_Néel.re`** at non-degenerate:
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re < 0` when `|A| ≥ 1`, `|¬A| ≥ 1`,
`N ≥ 1`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_neg_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re < 0 := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation]
  have hA_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have hAc_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hprod_pos :
      0 < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 := by
    positivity
  simp only [Complex.neg_re, Complex.div_ofNat_re,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im]
  linarith

end LatticeSystem.Quantum
