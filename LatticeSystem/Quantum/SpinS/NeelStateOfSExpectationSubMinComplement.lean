import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinComplementRe

/-!
# Néel expectation vs orientation-pair min: gap = `max(|A|, |¬A|)·N`

PR #3011: `min((pmA).re, (pm¬A).re) = −|A|·|¬A|·N²/2 −
max(|A|, |¬A|)·N`.

Néel expectation: `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩ = −|A|·|¬A|·N²/2`
(operator-level, PR #1178/#1193).

Subtracting (the quadratic term cancels):

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min((pmA).re, (pm¬A).re) = max(|A|, |¬A|)·N`

unconditionally. Together with the established gap to predictedSymm
(= max(|A|, |¬A|)·N − ||A| − |¬A||·N = min(|A|, |¬A|)·N), this gives
the operator–algebraic affine triangle:
- Néel expectation − min                = max(|A|, |¬A|)·N (this PR).
- Néel expectation − predictedSymm     = min(|A|, |¬A|)·N (existing).
- Néel expectation − avg                = |Λ|·N/2          (PR #3051).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel expectation sits `max(|A|, |¬A|)·N` above the orientation-pair min**:

  `⟨Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)⟩.re − min(...) = max(|A|, |¬A|)·N`

unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) (A := A) (N := N)
  have hmin := bipartiteToyMinEnergyPredicted_min_complement_re_eq (Λ := Λ) A N
  -- ⟨Néel⟩ = predictedSymm + min(|A|,|¬A|)·N (in ℂ).
  have hneel_eq : dotProduct (star (neelStateOfS A N))
      ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (neelStateOfS A N)) =
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N +
        ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) := by linear_combination hgap
  rw [hneel_eq]
  -- Compute predictedSymm.re via the predictedSymm formula.
  have hsymm_re : (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2) -
        (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) := by
    unfold bipartiteToyMinEnergyPredictedSymm
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
      mul_zero, zero_mul, sub_zero, add_zero]
  -- (a + b).re = a.re + b.re, and `(↑n * ↑N : ℂ).re = (n*N : ℝ)`.
  rw [Complex.add_re]
  have hprod_re : (((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) : ℂ) * (N : ℂ)).re =
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) := by
    rw [Complex.mul_re]
    simp [Complex.natCast_re, Complex.natCast_im]
  rw [hprod_re, hsymm_re, hmin]
  push_cast [Nat.cast_min]
  ring

end LatticeSystem.Quantum
