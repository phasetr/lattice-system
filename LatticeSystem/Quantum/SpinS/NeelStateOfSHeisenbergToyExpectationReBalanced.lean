import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightEqZeroIff

/-!
# Balanced-case Néel-state toy-Hamiltonian expectation: `−|Λ|²·N²/8`

PR #2886 gave the Néel expectation in `‖biw‖²` form:

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = ‖biw‖²/2 − |Λ|²·N²/8`.

At balanced sublattices (`|A| = |¬A|`, `N ≥ 1`), `‖biw‖ = 0`
(PR #2854 `bipartiteImbalanceWeight_eq_zero_iff`), so the
expectation collapses to

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = −|Λ|²·N²/8`.

This is the variational AFM-energy upper bound at balanced: the
Néel state achieves energy `−|Λ|²·N²/8`, providing a concrete
variational benchmark for the actual ground-state energy.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced-case Néel toy-Hamiltonian expectation real part**:
at `|A| = |¬A|`, `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = −|Λ|²·N²/8`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_balanced
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
      -((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_via_imbalance_norm_sq]
  have hbiw_zero :=
    (bipartiteImbalanceWeight_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr h
  have hbiw_norm_zero :
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 := by
    rw [hbiw_zero]; exact norm_zero
  rw [hbiw_norm_zero]
  ring

end LatticeSystem.Quantum
