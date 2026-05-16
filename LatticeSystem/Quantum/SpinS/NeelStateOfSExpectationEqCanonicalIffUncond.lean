import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalPredicted

/-!
# `⟨Néel⟩.re = (pmA).re ↔ |¬A| = 0 ∨ N = 0` unconditionally

PR #3053: `⟨Néel⟩.re − (pmA).re = |¬A|·N`.

  `⟨Néel⟩.re = (predicted_min A).re ↔ |¬A| = 0 ∨ N = 0`.

Unconditional version of PR #3060 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = pmA iff `|¬A| = 0 ∨ N = 0`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_canonical_predicted_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq
    (Λ := Λ) A N
  constructor
  · intro heq
    have hgap_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp hgap_zero with hAc | hN
    · left; exact_mod_cast hAc
    · right; exact_mod_cast hN
  · intro hor
    rcases hor with hAc | hN
    · have hAc_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hAc
      have hgap_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) = 0 := by rw [hAc_re]; ring
      linarith
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have hgap_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) = 0 := by rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
