import LatticeSystem.Quantum.SpinDot

/-!
# Two-site spin product matrix entry on swap-related configurations

This module computes the matrix entry of the two-site spin product
`Ŝ_x · Ŝ_y` at configurations related by the bond swap
`basisSwap σ x y` (with `x ≠ y`, antiparallel `σ_x ≠ σ_y`):

  `(Ŝ_x · Ŝ_y)_{σ, basisSwap σ x y} = 1/2`.

This is the off-diagonal matrix entry that, combined with the
Marshall sign trick (PR α-3), gives the explicit value of the
dressed Heisenberg matrix entry needed for the Perron–Frobenius
irreducibility argument (subsequent PRs).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (proof of Theorem 2.2).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The off-diagonal matrix entry of `Ŝ_x · Ŝ_y` at swap-related
configurations. For `x ≠ y` and `σ_x ≠ σ_y`,
`(spinHalfDot x y)(σ, basisSwap σ x y) = 1/2`.

Proof: by the antiparallel action lemma
`spinHalfDot_mulVec_basisVec_antiparallel`, applying `Ŝ_x · Ŝ_y` to
`basisVec (basisSwap σ x y)` gives
`(1/2) basisVec (basisSwap (basisSwap σ x y) x y) - (1/4) basisVec (basisSwap σ x y)
 = (1/2) basisVec σ - (1/4) basisVec (basisSwap σ x y)`
(by involutivity). Evaluating at `σ` (which is distinct from
`basisSwap σ x y`) gives `1/2 · 1 - 1/4 · 0 = 1/2`. -/
theorem spinHalfDot_apply_basisSwap
    {x y : Λ} (hxy : x ≠ y) {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    (spinHalfDot x y) σ (basisSwap σ x y) = (1 / 2 : ℂ) := by
  -- Express the matrix entry as `((spinHalfDot x y).mulVec
  -- (basisVec (basisSwap σ x y))) σ` via the dotProduct expansion.
  have happly :
      ((spinHalfDot x y).mulVec (basisVec (basisSwap σ x y))) σ =
        (spinHalfDot x y) σ (basisSwap σ x y) := by
    change dotProduct (fun j => (spinHalfDot x y) σ j) (basisVec (basisSwap σ x y))
      = _
    unfold dotProduct
    rw [sum_mul_basisVec (basisSwap σ x y) ((spinHalfDot x y) σ)]
  rw [← happly]
  -- The configuration `basisSwap σ x y` is antiparallel at `(x, y)`
  -- since `σ_x ≠ σ_y`.
  have hba : (basisSwap σ x y) x ≠ (basisSwap σ x y) y :=
    basisSwap_antiparallel hxy σ h
  -- Apply the antiparallel action lemma.
  rw [spinHalfDot_mulVec_basisVec_antiparallel hxy (basisSwap σ x y) hba]
  -- The result is `(1/2) · basisVec (basisSwap (swap σ) x y) - (1/4) · basisVec (swap σ)`.
  -- By involutivity: `basisSwap (basisSwap σ x y) x y = σ`.
  rw [basisSwap_involutive hxy σ]
  -- Evaluate at `σ`: `(1/2) · basisVec σ σ - (1/4) · basisVec (swap σ) σ = 1/2 - 0`.
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_self]
  rw [basisVec_of_ne (basisSwap_ne_self hxy h).symm]
  ring

end LatticeSystem.Quantum
