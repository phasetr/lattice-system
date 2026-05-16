import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# `⟨Néel⟩.re = avg ↔ |Λ| = 0 ∨ N = 0` unconditionally

PR #3051: `⟨Néel⟩.re − avg = |Λ|·N / 2`.

This vanishes iff one of the factors is zero:

  `⟨Néel⟩.re = ((pmA).re + (pm¬A).re) / 2 ↔ |Λ| = 0 ∨ N = 0`.

Unconditional version of PR #3062 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = avg iff `|Λ| = 0 ∨ N = 0`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_avg_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      Fintype.card Λ = 0 ∨ N = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  constructor
  · intro heq
    have hgap_zero : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by linarith
    have hprod_zero : (Fintype.card Λ : ℝ) * (N : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp hprod_zero with hΛ | hN
    · left; exact_mod_cast hΛ
    · right; exact_mod_cast hN
  · intro hor
    rcases hor with hΛ | hN
    · have hΛ_re : (Fintype.card Λ : ℝ) = 0 := by exact_mod_cast hΛ
      have hgap_zero : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by
        rw [hΛ_re]; ring
      linarith
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have hgap_zero : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by
        rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
