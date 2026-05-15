import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementSaturatedEqMMaxQuad
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementLtMMaxQuadNondegenerate

/-!
# Iff: complement predicted `(Ŝ_tot)²` eigenvalue `= m_max·(m_max+1)` iff `|A| = 0`

PR #2941 gave the complement-saturated equality (backward): `|A| = 0`
implies complement-orientation `eigenvalue.re = m_max·(m_max+1)`.

PR #2946 gave the strict bound at non-degenerate (`|A| ≥ 1`, `|¬A| ≥ 1`,
`N ≥ 1`, orientation `|A| ≤ |¬A|`): complement_eigenvalue
`< m_max·(m_max+1)`. Taking contrapositive (forward) with the
orientation: at `|A| ≤ |¬A|`, `N ≥ 1`, if complement_eigenvalue equals
`m_max·(m_max+1)`, then `|A| = 0` (using `|A| ≤ |¬A|` to derive
`|¬A| ≥ 1` from `|A| ≥ 1`).

Mirror of PR #2948.

  `complement_eigenvalue.re = m_max·(m_max + 1) ↔ |A| = 0`
  at `|A| ≤ |¬A|`, `N ≥ 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff characterisation (complement)**: complement-orientation
predicted `(Ŝ_tot)²` eigenvalue `= m_max·(m_max+1)` ↔ `|A| = 0`
(at `|A| ≤ |¬A|`, `N ≥ 1`). Mirror of PR #2948. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_iff_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by
  constructor
  · intro heq
    by_contra hne
    have hA_pos : 0 <
        (Finset.univ.filter (fun x : Λ => A x = true)).card :=
      Nat.pos_of_ne_zero hne
    have hAc_pos : 0 <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      lt_of_lt_of_le hA_pos horient
    have hlt :=
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_nondegenerate
        A N horient hA_pos hAc_pos hN
    linarith
  · intro h
    exact bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_of_cardA_zero
      A N h

end LatticeSystem.Quantum
