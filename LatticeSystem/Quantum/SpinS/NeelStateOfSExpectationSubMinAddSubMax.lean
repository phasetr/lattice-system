import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMaxComplement

/-!
# Additive identity: `(⟨Néel⟩ − min) + (⟨Néel⟩ − max) = |Λ|·N`

Existing (PR #3052): `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`.
Existing (PR #3129): `⟨Néel⟩.re − max(...) = min(|A|, |¬A|)·N`.

Sum: `min(|A|, |¬A|) + max(|A|, |¬A|) = |A| + |¬A| = |Λ|`, so

  `(⟨Néel⟩.re − min(...)) + (⟨Néel⟩.re − max(...)) = |Λ|·N`

unconditionally. Equivalent to `2·(⟨Néel⟩.re − avg) = |Λ|·N`, consistent
with `⟨Néel⟩.re − avg = |Λ|·N/2` (PR #3051).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Sum of the two gaps equals `|Λ|·N`** unconditionally:

  `(⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min(...)) + (⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max(...))
    = |Λ|·N`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_add_sub_max_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    ((dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) +
      ((dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) =
      (Fintype.card Λ : ℝ) * (N : ℝ) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq,
      neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq]
  -- Goal: max·N + min·N = |Λ|·N. Reduces to min + max = |Λ|.
  have hsum : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) +
      max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    min_add_max _ _
  have hcard : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
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
  linear_combination (N : ℝ) * hsum + (N : ℝ) * hcard

end LatticeSystem.Quantum
