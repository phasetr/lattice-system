import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelBasisVecS

/-!
# Linear transverse Néel expectations vanish: `(Ŝ_tot^(1))_Néel.re = 0`,
`(Ŝ_tot^(2))_Néel.re = 0`

The linear total-spin transverse-axis expectations on the Néel
state vanish identically (PR #1295 / γ-4 step 241):

  `<Φ_Néel|Ŝ_tot^(1)|Φ_Néel> = 0`,
  `<Φ_Néel|Ŝ_tot^(2)|Φ_Néel> = 0`.

Real-part forms follow directly (`Complex.zero_re = 0`):

  `(<Φ_Néel|Ŝ_tot^(1)|Φ_Néel>).re = 0`,
  `(<Φ_Néel|Ŝ_tot^(2)|Φ_Néel>).re = 0`.

Completes the linear part of the operator-level decomposition of
Néel's `Ŝ_tot`:
- z-axis: `biw.re` (PR #2905),
- transverse: `0` (this PR).

Combined with the squared decomposition (PRs #2904, #2906) gives
the full picture: the Néel state is in a definite z-axis
magnetization sector (`M = biw.re`) but spreads over the
transverse axes (`(Ŝ_tot^(1,2))² > 0` on average, despite linear = 0).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-state `Ŝ_tot^(1)` linear expectation real part = 0**. -/
theorem neelStateOfS_totalSpinSOp1_expectation_re_eq_zero :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N).mulVec (neelStateOfS A N))).re = 0 := by
  rw [neelStateOfS_totalSpinSOp1_expectation]
  exact Complex.zero_re

/-- **Néel-state `Ŝ_tot^(2)` linear expectation real part = 0**. -/
theorem neelStateOfS_totalSpinSOp2_expectation_re_eq_zero :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp2 Λ N).mulVec (neelStateOfS A N))).re = 0 := by
  rw [neelStateOfS_totalSpinSOp2_expectation]
  exact Complex.zero_re

end LatticeSystem.Quantum
