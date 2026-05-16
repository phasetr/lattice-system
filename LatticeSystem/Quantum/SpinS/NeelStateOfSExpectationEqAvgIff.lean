import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# Néel expectation = avg iff `|Λ| = 0` at `N ≥ 1`

PR #3051: `⟨Néel⟩.re − avg = |Λ|·N/2`. At `N ≥ 1`:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re = avg ↔ |Λ| = 0`.

The Néel state attains the orientation-pair midpoint only on the
empty lattice — at any positive lattice with positive spin, the
Néel state strictly exceeds the midpoint of the two orientation-
specific predicted min energies.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩ = avg iff `|Λ| = 0` at `N ≥ 1`**. Equality version of PR #3058. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_avg_complement_re_iff_card_zero
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      Fintype.card Λ = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : ((N : ℝ)) ≠ 0 := ne_of_gt hN_re
  constructor
  · intro heq
    have hgap_zero : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by linarith
    have hprod_zero : (Fintype.card Λ : ℝ) * (N : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp hprod_zero with h | h
    · exact_mod_cast h
    · exact absurd h hN_ne
  · intro hcard
    have hcard_re : (Fintype.card Λ : ℝ) = 0 := by exact_mod_cast hcard
    have hgap_zero : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by rw [hcard_re]; ring
    linarith

end LatticeSystem.Quantum
