import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `bipartiteImbalanceWeight` via signed integer imbalance

PR #2825 realises `bipartiteImbalanceWeight A N` as the lift of
`((|A| − |¬A|) · N / 2 : ℝ)`. This file expresses the same
quantity via the **integer** signed imbalance
`(|A| : ℤ) − (|¬A| : ℤ)`, the canonical signed sublattice
imbalance used in Tasaki §2.5 Theorem 2.3's discrete
combinatorial bookkeeping:

  `bipartiteImbalanceWeight A N
     = (((|A| : ℤ) − (|¬A| : ℤ)) : ℂ) · (N : ℂ) / 2`.

Useful when reasoning about signs / orientation flips without
going through the real-axis representation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Integer-imbalance form of `bipartiteImbalanceWeight`**:
`bipartiteImbalanceWeight A N
     = (((|A| − |¬A|) : ℤ) : ℂ) · N / 2`. -/
theorem bipartiteImbalanceWeight_eq_intCast :
    bipartiteImbalanceWeight (Λ := Λ) A N =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℤ) :
            ℤ) : ℂ) * (N : ℂ) / 2 := by
  unfold bipartiteImbalanceWeight
  push_cast
  ring

end LatticeSystem.Quantum
