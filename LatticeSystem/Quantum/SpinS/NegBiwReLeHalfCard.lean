import LatticeSystem.Quantum.SpinS.BiwNormLeHalfCard

/-!
# `−biw.re ≤ |Λ|·N/2` unconditionally

Mirror of PR #3291. The negative of the real part of the bipartite
imbalance weight is bounded above by its norm, which is bounded above
by `|Λ|·N/2`:

  `−biw.re ≤ ‖biw‖ ≤ |Λ|·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`−biw.re ≤ |Λ|·N/2`** unconditionally. Mirror of PR #3291. -/
theorem bipartiteImbalanceWeight_neg_re_le_half_card
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    -(bipartiteImbalanceWeight (Λ := Λ) A N).re ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  classical
  have h_re_le_norm : -(bipartiteImbalanceWeight (Λ := Λ) A N).re ≤
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
    have h := Complex.re_le_norm (-(bipartiteImbalanceWeight (Λ := Λ) A N))
    rwa [Complex.neg_re, norm_neg] at h
  have h_norm_le := bipartiteImbalanceWeight_norm_le_half_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
