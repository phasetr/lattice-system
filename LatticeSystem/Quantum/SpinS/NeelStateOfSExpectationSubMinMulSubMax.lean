import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMaxComplement

/-!
# Multiplicative identity: `(⟨Néel⟩ − min) · (⟨Néel⟩ − max) = |A|·|¬A|·N²`

Existing (PR #3052): `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`.
Existing (PR #3129): `⟨Néel⟩.re − max(...) = min(|A|, |¬A|)·N`.

Product: `min(|A|, |¬A|) · max(|A|, |¬A|) = |A| · |¬A|`, so

  `(⟨Néel⟩.re − min(...)) · (⟨Néel⟩.re − max(...)) = |A| · |¬A| · N²`

unconditionally. This connects the operator-algebraic gaps directly to
the leading quadratic term `−|A|·|¬A|·N²/2` in the predicted minimum
energy: the product of gaps equals `−2 · (predicted quadratic part)`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Product of the two gaps equals `|A| · |¬A| · N²`** unconditionally:

  `(⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min(...)) · (⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max(...))
    = |A| · |¬A| · N²`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_mul_sub_max_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    ((dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) *
      ((dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq,
      neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq]
  -- Goal: (max·N) · (min·N) = |A| · |¬A| · (N·N).
  have hprod : max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    rw [mul_comm (max _ _) (min _ _)]
    exact min_mul_max _ _
  linear_combination ((N : ℝ) * (N : ℝ)) * hprod

end LatticeSystem.Quantum
