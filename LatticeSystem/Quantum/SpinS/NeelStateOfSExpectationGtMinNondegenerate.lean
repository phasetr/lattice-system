import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement

/-!
# Néel expectation strictly above orientation-pair min at `|Λ| ≥ 1` ∧ `N ≥ 1`

PR #3052: `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`. Strict when
`max(|A|, |¬A|) ≥ 1` and `N ≥ 1`. Since `|A| + |¬A| = |Λ|` (cardinality
partition), `max(|A|, |¬A|) ≥ 1` whenever `|Λ| ≥ 1` (the larger
sublattice can't be empty if their sum is positive). Hence:

  `0 < |Λ|, 0 < N → min(...) < ⟨Néel⟩.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel > min at `|Λ| ≥ 1` and `N ≥ 1`**. Strict version of PR #3052. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_min_complement_re
    (A : Λ → Bool) (N : ℕ)
    (hΛ : 0 < Fintype.card Λ)
    (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq
    (Λ := Λ) A N
  -- max(|A|, |¬A|) ≥ 1 from |A| + |¬A| = |Λ| ≥ 1.
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
  -- max as real of two non-neg reals ≥ each. Need: max ≥ 1.
  have hmax_re_pos : (0 : ℝ) < max
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    have hΛ_pos : 0 < ((Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) := by rw [hsum]; exact hΛ
    have hA_or_Ac : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∨
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
      by_contra h
      push Not at h
      obtain ⟨h1, h2⟩ := h
      have h1' : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := Nat.le_zero.mp h1
      have h2' : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := Nat.le_zero.mp h2
      omega
    rcases hA_or_Ac with hA | hAc
    · have : (0 : ℝ) < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
        exact_mod_cast hA
      exact lt_of_lt_of_le this (le_max_left _ _)
    · have : (0 : ℝ) <
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hAc
      exact lt_of_lt_of_le this (le_max_right _ _)
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < max
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) :=
    mul_pos hmax_re_pos hN_re
  linarith

end LatticeSystem.Quantum
