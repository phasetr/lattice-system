import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementRe

/-!
# Néel expectation vs orientation-pair average: gap = `|Λ|·N / 2`

The Néel-state toy-Hamiltonian expectation equals `−|A|·|¬A|·N²/2`
(operator-level result, PR #1178/#1193). The orientation-pair
average is `avg = −|A|·|¬A|·N²/2 − |Λ|·N/2` (PR #3033).

Subtracting (the `−|A|·|¬A|·N²/2` term cancels):

  `⟨Φ_Néel | Ĥ_toy | Φ_Néel⟩ − avg = |Λ|·N / 2`

unconditionally. This bridges the operator-level Néel state expectation
with the algebraic orientation-pair midpoint:
- Néel expectation sits exactly `|Λ|·N/2` above the orientation-pair
  average.
- predictedSymm sits `min(|A|, |¬A|)·N` below the Néel expectation
  (existing PR result).
- avg sits `|Λ|·N/2 − min(|A|, |¬A|)·N = max(|A|, |¬A|)·N/2 −
  min(|A|, |¬A|)·N/2 = ||A| − |¬A||·N/2` below predictedSymm
  (PR #3034).

Together this gives the affine chain:
  `avg + |Λ|·N/2 = ⟨Néel⟩`,
  `avg + ||A| − |¬A||·N/2 = predictedSymm`,
  `avg − ||A| − |¬A||·N/2 = min`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel expectation sits `|Λ|·N/2` above the orientation-pair average**:

  `⟨Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)⟩.re − avg = |Λ|·N / 2`

unconditionally. Connects the operator-level Néel expectation with
the algebraic orientation-pair midpoint. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  -- Use the Gap theorem and the avg formula.
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) (A := A) (N := N)
  have havg := bipartiteToyMinEnergyPredicted_avg_complement_re_eq (Λ := Λ) A N
  -- ⟨Néel⟩ = predictedSymm + min(|A|,|¬A|)·N (in ℂ).
  have hneel_eq : dotProduct (star (neelStateOfS A N))
      ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (neelStateOfS A N)) =
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N +
        ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) := by linear_combination hgap
  rw [hneel_eq]
  -- Take .re; use predictedSymm.re formula.
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
      mul_zero, zero_mul, sub_zero]
    push_cast [Nat.cast_min]
    ring
  simp only [Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero]
  rw [hsymm_re, havg]
  push_cast [Nat.cast_min]
  -- Use |A| + |¬A| = |Λ|.
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    classical
    have hN' : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
      rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases A x <;> simp
      · rw [Finset.disjoint_filter]
        intro x _ hx
        simp [hx]
    exact_mod_cast hN'
  -- Now linarith with min + max = sum identity for reals.
  have hmin_max : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) +
      max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    min_add_max _ _
  linarith

end LatticeSystem.Quantum
