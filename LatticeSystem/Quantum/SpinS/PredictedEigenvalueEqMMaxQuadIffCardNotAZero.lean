import LatticeSystem.Quantum.SpinS.PredictedEigenvalueSaturatedEqMMaxQuad
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueLtMMaxQuadOfCardNotAPos

/-!
# Iff characterisation: predicted `(Ŝ_tot)²` eigenvalue `= m_max·(m_max+1)` iff `|¬A| = 0`

PR #2938 gave the saturated-edge equality (backward): `|¬A| = 0`
implies `eigenvalue.re = m_max·(m_max+1)`.

PR #2947 gave the strict bound at `|¬A| ≥ 1`, `N ≥ 1`: eigenvalue
`< m_max·(m_max+1)`. Taking contrapositive (forward): if `N ≥ 1` and
`eigenvalue.re = m_max·(m_max+1)`, then `|¬A| = 0`.

Combining at `N ≥ 1`:

  `eigenvalue.re = m_max·(m_max + 1) ↔ |¬A| = 0`.

This is the equality characterisation for the `(s_A − s_B)` orientation:
the predicted Casimir hits the fully-polarised ferromagnetic value
**iff** all sites are in `A` (saturated edge).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff characterisation**: predicted `(Ŝ_tot)²` eigenvalue
`= m_max·(m_max+1)` ↔ `|¬A| = 0` (at `N ≥ 1`). -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_iff_cardNotA_zero
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  constructor
  · intro heq
    by_contra hne
    have hAc_pos : 0 <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      Nat.pos_of_ne_zero hne
    have hlt :=
      bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_cardNotA_pos
        A N hAc_pos hN
    linarith
  · intro h
    exact bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_of_cardNotA_zero
      A N h

end LatticeSystem.Quantum
