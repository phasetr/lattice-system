import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergUniformEigenvalue

/-!
# Explicit saturated-FM eigenvalue for uniform J: combinatorial simplification

For uniform `J(x, y) = 1`, the explicit combinatorial form of
PR #951 simplifies to `m_max(m_max + 1) = (|V|·N/2)·(|V|·N/2 + 1)`:

  `∑_x ∑_y (if x = y then N(N+2)/4 else (N/2)²)
    = |V|·N(N+2)/4 + |V|(|V|−1)·N²/4
    = (|V|·N/2)·(|V|·N/2 + 1)`.

Direct combinatorial calculation, with `Finset.sum_const` for the
constant inner sums and `(N+2)/4 + (|V|−1)·N/4 = (|V|·N + 2)/4`
as the algebraic key step.

This combines PR #951 (explicit form) with PR #949 (uniform = Casimir)
into a single closed-form simplification.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Combinatorial simplification:
`∑_x ∑_y (1 · (if x = y then N(N+2)/4 else (N/2)²)) = m_max(m_max + 1)`. -/
theorem explicit_uniform_eq_casimir_eigenvalue [Nonempty V] :
    (∑ x : V, ∑ y : V,
        (1 : ℂ) * (if x = y then (N : ℂ) * (N + 2) / 4
                   else (N : ℂ) / 2 * ((N : ℂ) / 2))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) := by
  -- Combine PR #951 (explicit form) and PR #949 (uniform = Casimir).
  have h_explicit := saturatedFerromagnetEigenvalueS_explicit
    (V := V) (N := N) (fun (_ : V) (_ : V) => (1 : ℂ))
  have h_uniform := saturatedFerromagnetEigenvalueS_uniform (V := V) (N := N)
  unfold saturatedFerromagnetCasimirEigenvalueS at h_uniform
  rw [h_explicit] at h_uniform
  exact h_uniform

end LatticeSystem.Quantum
