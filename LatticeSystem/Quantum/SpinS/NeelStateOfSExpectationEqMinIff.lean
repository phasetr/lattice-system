import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement

/-!
# Néel expectation = orientation-pair min iff `|Λ| = 0` at `N ≥ 1`

PR #3052: `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`. This vanishes
iff `max(|A|, |¬A|)·N = 0`, i.e. `max = 0 ∨ N = 0`. Since
`max(|A|, |¬A|) = 0 ↔ |A| = 0 ∧ |¬A| = 0 ↔ |Λ| = 0` (using
`|A| + |¬A| = |Λ|`), at `N ≥ 1`:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re = min(...) ↔ |Λ| = 0`.

The Néel state attains the orientation-pair min only on the empty
lattice.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩ = min iff `|Λ| = 0` at `N ≥ 1`**. Equality version of PR #3059. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_min_complement_re_iff_card_zero
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      Fintype.card Λ = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq
    (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : ((N : ℝ)) ≠ 0 := ne_of_gt hN_re
  classical
  have hsum : (Finset.univ.filter (fun x : Λ => A x = true)).card +
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
    rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases A x <;> simp
    · rw [Finset.disjoint_filter]
      intro x _ hx
      simp [hx]
  constructor
  · intro heq
    have hmax_mul_zero : max
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmax_mul_zero with hmax_zero | hN_zero
    · have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
        positivity
      have hcB_nn : (0 : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by positivity
      have hcA_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        have := le_max_left
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
        linarith
      have hcB_zero :
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        have := le_max_right
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
        linarith
      have hcA_nat : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by
        exact_mod_cast hcA_zero
      have hcB_nat : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
        exact_mod_cast hcB_zero
      omega
    · exact absurd hN_zero hN_ne
  · intro hcard
    have hcA_nat : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by omega
    have hcB_nat : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by omega
    have hcA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
      exact_mod_cast hcA_nat
    have hcB_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
      exact_mod_cast hcB_nat
    have hmax_zero : max
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
      rw [hcA_re, hcB_re]; simp
    have hmax_mul_zero : max
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
      rw [hmax_zero]; ring
    linarith

end LatticeSystem.Quantum
