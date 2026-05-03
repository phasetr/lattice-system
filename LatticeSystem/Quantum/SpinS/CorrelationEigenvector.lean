import LatticeSystem.Quantum.SpinS.CorrelationSumCasimir

/-!
# Correlation sum on `Ŝ_tot²`-eigenvectors

For a `Ŝ_tot²`-eigenvector `Φ` at eigenvalue `lam`, the total
two-site correlation sum equals `lam · ⟨Φ, Φ⟩`:

  `∑_{x, y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = lam · ⟨Φ, Φ⟩`.

For normalized `Φ`, this simplifies to `lam`. The off-diagonal part
follows by subtracting the universal diagonal `|V|·S(S+1) ·
⟨Φ, Φ⟩` (PR #920):

  `∑_{x ≠ y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = lam − |V|·S(S+1)` (normalized).

Generalises PR #929 (`lam = 0` ⟹ sum = 0).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- For a `Ŝ_tot²`-eigenvector `Φ` at eigenvalue `lam`,
the total correlation sum equals `lam · ⟨Φ, Φ⟩`. -/
theorem totalSpinSSquared_eigenvector_correlation_full_sum
    {lam : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared V N).mulVec Φ = lam • Φ) :
    ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) =
      lam * dotProduct (star Φ) Φ := by
  rw [correlation_full_sum_eq_totalSpinSSquared_expectation]
  rw [hΦ, dotProduct_smul, smul_eq_mul]

/-- For a normalized `Ŝ_tot²`-eigenvector at eigenvalue `lam`,
the total correlation sum equals `lam`. -/
theorem totalSpinSSquared_eigenvector_correlation_full_sum_normalized
    {lam : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared V N).mulVec Φ = lam • Φ)
    (hΦ_norm : dotProduct (star Φ) Φ = 1) :
    ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) = lam := by
  rw [totalSpinSSquared_eigenvector_correlation_full_sum hΦ, hΦ_norm, mul_one]

end LatticeSystem.Quantum
