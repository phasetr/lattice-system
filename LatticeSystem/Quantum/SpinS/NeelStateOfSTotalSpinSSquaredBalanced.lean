import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightEqZeroIff

/-!
# Balanced-case Néel `(Ŝ_tot)²` expectation: `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = |Λ|·N/2`

PR #2896 gave the form

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`.

At balanced sublattices (`|A| = |¬A|`, `N ≥ 1`), the imbalance
weight vanishes (PR #2854 `bipartiteImbalanceWeight_eq_zero_iff`),
so `‖biw‖ = 0` and the expectation collapses to

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = |Λ|·N/2`.

This is the minimum value of the `(Ŝ_tot)²` expectation across
all bipartitions (since `‖biw‖² ≥ 0` always). For Tasaki §2.5
Theorem 2.3 (γ-4): at balanced sublattices the Néel state's total
spin is `(Ŝ_tot)² = m_max·1` (not `S_tot·(S_tot+1)` for any
specific `S_tot` — Néel is **not** a `(Ŝ_tot)²` eigenvector at
balanced).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced Néel `(Ŝ_tot)²` expectation = `|Λ|·N/2`**:
at `|A| = |¬A|` and `N ≥ 1`,
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = |Λ|·N/2`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_balanced
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq]
  -- ‖biw‖ = 0 at balanced.
  have hbiw_zero :=
    (bipartiteImbalanceWeight_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr h
  have hbiw_norm_zero :
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 := by
    rw [hbiw_zero]; exact norm_zero
  rw [hbiw_norm_zero]
  ring

end LatticeSystem.Quantum
