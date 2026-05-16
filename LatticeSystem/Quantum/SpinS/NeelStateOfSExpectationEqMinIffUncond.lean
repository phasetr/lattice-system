import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement

/-!
# `⟨Néel⟩.re = min(...) ↔ |Λ| = 0 ∨ N = 0` unconditionally

PR #3052: `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`.

This vanishes iff `max(|A|, |¬A|)·N = 0`, iff `max = 0 ∨ N = 0`. Since
`max(|A|, |¬A|) = 0 ↔ |Λ| = 0` (via `|A| + |¬A| = |Λ|`):

  `⟨Néel⟩.re = min((pmA).re, (pm¬A).re) ↔ |Λ| = 0 ∨ N = 0`.

Unconditional version of PR #3063 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = min iff `|Λ| = 0 ∨ N = 0`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_min_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      Fintype.card Λ = 0 ∨ N = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq
    (Λ := Λ) A N
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
    have hgap_zero : max
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hgap_zero with hmax | hN
    · -- max(...) = 0 → both = 0 (since ≥ 0) → |Λ| = 0.
      have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
        positivity
      have hcAc_nn : (0 : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by positivity
      have hcA_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        have := le_max_left
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
        linarith
      have hcAc_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        have := le_max_right
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
        linarith
      have hcA_nat : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by
        exact_mod_cast hcA_zero
      have hcAc_nat : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
        exact_mod_cast hcAc_zero
      left; omega
    · right; exact_mod_cast hN
  · intro hor
    rcases hor with hΛ | hN
    · have hcA_nat : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by omega
      have hcAc_nat : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by omega
      have hcA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hcA_nat
      have hcAc_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hcAc_nat
      have hmax_zero : max
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hcA_re, hcAc_re]; simp
      have hgap_zero : max
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
        rw [hmax_zero]; ring
      linarith
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have hgap_zero : max
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
        rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
