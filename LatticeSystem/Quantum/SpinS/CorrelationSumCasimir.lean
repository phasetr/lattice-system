import LatticeSystem.Quantum.SpinS.SingletCorrelationSum
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Two-site correlation sum equals Casimir expectation

For ANY state `Φ` on the multi-site spin-`S` Hilbert space, the
sum of all two-site correlations equals the Casimir expectation:

  `∑_{x : V} ∑_{y : V} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = ⟨Φ, Ŝ_tot² · Φ⟩`.

This is the universal version of PR #929's singlet specialisation
(`Ŝ_tot² Φ = 0` ⟹ sum = 0). Direct from
`totalSpinSSquared_eq_sum_spinSDot` lifted to `dotProduct` via
`Matrix.sum_mulVec` + `dotProduct_sum` linearity.

Specialised to `Ŝ_tot²`-eigenvectors at eigenvalue `λ` (and for
normalized states):

  `∑_{x ≠ y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = λ − |V|·N(N+2)/4`

(diagonal `|V|·S(S+1)` from PR #920 contribution subtracted).

For the saturated-ferromagnet `|σ_⊤⟩` (Casimir eigenvalue
`m_max(m_max+1)`, `m_max = |V|·N/2`):
- Total sum = `m_max(m_max+1)`.
- Off-diagonal = `m_max(m_max+1) − |V|·S(S+1)`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The full two-site correlation sum equals the Casimir expectation:

  `∑_{x, y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = ⟨Φ, Ŝ_tot² · Φ⟩`.

Direct from `totalSpinSSquared_eq_sum_spinSDot` lifted to
`dotProduct` via `Matrix.sum_mulVec` + `dotProduct_sum`. -/
theorem correlation_full_sum_eq_totalSpinSSquared_expectation
    (Φ : (V → Fin (N + 1)) → ℂ) :
    ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) =
      dotProduct (star Φ) ((totalSpinSSquared V N).mulVec Φ) := by
  rw [totalSpinSSquared_eq_sum_spinSDot]
  rw [Matrix.sum_mulVec]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.sum_mulVec]
  rw [dotProduct_sum]

/-- For the saturated-ferromagnet state `|σ_⊤⟩` (highest weight),
the total two-site correlation sum equals `m_max(m_max + 1) =
(|V|·N/2)(|V|·N/2 + 1)`. -/
theorem allAlignedStateS_zero_correlation_full_sum
    [Nonempty V] :
    ∑ x : V, ∑ y : V,
        dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
          ((spinSDot x y N).mulVec
            (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) := by
  rw [correlation_full_sum_eq_totalSpinSSquared_expectation]
  exact allAlignedStateS_zero_expectation_totalSpinSSquared

/-- Symmetric for `|σ_⊥⟩`. -/
theorem allAlignedStateS_last_correlation_full_sum
    [Nonempty V] :
    ∑ x : V, ∑ y : V,
        dotProduct (star (allAlignedStateS V N (Fin.last N)))
          ((spinSDot x y N).mulVec
            (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) := by
  rw [correlation_full_sum_eq_totalSpinSSquared_expectation]
  exact allAlignedStateS_last_expectation_totalSpinSSquared

end LatticeSystem.Quantum
