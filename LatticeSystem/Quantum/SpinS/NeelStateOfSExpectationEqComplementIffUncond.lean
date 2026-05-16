import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubComplementPredicted

/-!
# `⟨Néel⟩.re = (pm¬A).re ↔ |A| = 0 ∨ N = 0` unconditionally

PR #3054: `⟨Néel⟩.re − (pm¬A).re = |A|·N`.

  `⟨Néel⟩.re = (predicted_min ¬A).re ↔ |A| = 0 ∨ N = 0`.

Mirror of PR #3110. Unconditional version of PR #3061.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = pm(¬A) iff `|A| = 0 ∨ N = 0`** unconditionally. Mirror of PR #3110. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_complement_predicted_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨ N = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq
    (Λ := Λ) A N
  constructor
  · intro heq
    have hgap_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        (N : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp hgap_zero with hA | hN
    · left; exact_mod_cast hA
    · right; exact_mod_cast hN
  · intro hor
    rcases hor with hA | hN
    · have hA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hA
      have hgap_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          (N : ℝ) = 0 := by rw [hA_re]; ring
      linarith
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have hgap_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          (N : ℝ) = 0 := by rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
