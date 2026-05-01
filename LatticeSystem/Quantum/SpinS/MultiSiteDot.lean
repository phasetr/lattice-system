import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Casimir

/-!
# Two-site spin-`S` inner product `Ŝ_x · Ŝ_y`
(Tasaki §2.5 Phase B-β β-3c)

For lattice sites `x, y : Λ` and spin parameter `N : ℕ` (with `N = 2S`),
the two-site inner product on the multi-site spin-`S` Hilbert space is

  `Ŝ_x · Ŝ_y := Σ_{α=1,2,3} onSiteS x Ŝ^{(α)} · onSiteS y Ŝ^{(α)}`.

This is the spin-`S` analogue of `spinHalfDot` (`Quantum/SpinDot/Core.lean`).

We record the basic symmetry `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x`, which for `x = y`
is trivial, and for `x ≠ y` follows from `onSiteS_mul_onSiteS_of_ne`
(β-3b). The Tasaki §2.2 (2.2.16)-style raising/lowering decomposition,
the same-site identity `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1`, and Hermiticity
will follow in subsequent PRs.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Two-site spin-`S` inner product
`Ŝ_x · Ŝ_y := Σ_{α=1,2,3} onSiteS x Ŝ^{(α)} · onSiteS y Ŝ^{(α)}`. -/
noncomputable def spinSDot (x y : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
    onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
    onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)

/-- Symmetry of the two-site dot product: `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x`. -/
theorem spinSDot_comm (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) = spinSDot y x N := by
  unfold spinSDot
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [onSiteS_mul_onSiteS_of_ne hxy (spinSOp1 N) (spinSOp1 N),
        onSiteS_mul_onSiteS_of_ne hxy (spinSOp2 N) (spinSOp2 N),
        onSiteS_mul_onSiteS_of_ne hxy (spinSOp3 N) (spinSOp3 N)]

/-- **Same-site Casimir**: `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1` on the
multi-site space, the lift of the single-site Casimir identity
`(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1` (β-14 of
Issue #458) to the many-body Hilbert space via `onSiteS`. -/
theorem spinSDot_self (x : Λ) (N : ℕ) :
    (spinSDot x x N : ManyBodyOpS Λ N) =
      ((N : ℂ) * (N + 2) / 4) • 1 := by
  unfold spinSDot
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same]
  rw [← onSiteS_add, ← onSiteS_add, spinSOp_total_squared,
      onSiteS_smul, onSiteS_one]

end LatticeSystem.Quantum
