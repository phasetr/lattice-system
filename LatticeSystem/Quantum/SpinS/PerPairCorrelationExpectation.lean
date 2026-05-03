import LatticeSystem.Quantum.SpinS.SpinSDotAllAlignedLast
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Per-pair `⟨Ŝ_x · Ŝ_y⟩ = N²/4` on the saturated states (`x ≠ y`)

For `x ≠ y` and `Φ ∈ {|σ_⊤⟩, |σ_⊥⟩}`,

  `⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = N²/4`.

Direct corollary of PRs #939 / #940 (eigenvalue equations) plus
PR #913 normalization. The per-pair correlation `S² = N²/4` is
the constant value attained on the saturated ferromagnet, with
total off-diagonal sum `|V|·(|V|-1) · S² = m_max(m_max+1) -
|V|·S(S+1)` matching PR #934.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `⟨|σ_⊤⟩, Ŝ_x · Ŝ_y · |σ_⊤⟩⟩ = N²/4` for `x ≠ y`. -/
theorem allAlignedStateS_zero_expectation_spinSDot_of_ne
    {x y : V} (hxy : x ≠ y) :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      ((spinSDot x y N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      (N : ℂ) * (N : ℂ) / 4 := by
  rw [spinSDot_mulVec_allAlignedStateS_zero_of_ne hxy]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

/-- `⟨|σ_⊥⟩, Ŝ_x · Ŝ_y · |σ_⊥⟩⟩ = N²/4` for `x ≠ y`. -/
theorem allAlignedStateS_last_expectation_spinSDot_of_ne
    {x y : V} (hxy : x ≠ y) :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((spinSDot x y N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      (N : ℂ) * (N : ℂ) / 4 := by
  rw [spinSDot_mulVec_allAlignedStateS_last_of_ne hxy]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

end LatticeSystem.Quantum
