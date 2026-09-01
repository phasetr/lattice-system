import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D

/-!
# Signature pin: `shastry_staggered_susceptibility_subcubic`

Red-first pin (Tasaki §4.1 Corollary 4.3 rename, PR #5414): `shastry_staggered_susceptibility_bound`
(`∃ C ≥ 0, ∀ L, … ≤ C·L`) is false as quantified (odd `N` makes `χ/L → ∞`), and is replaced by the
weaker, correctly-quantified `shastry_staggered_susceptibility_subcubic`
(`∀ δ > 0, ∃ L₀, ∀ L ≥ L₀, … ≤ δ·L³`). This file is not expected to build until the new axiom is
declared: it pins the exact shape the sole consumer (`no_long_range_order_1d_of_susceptibility`,
`NoLongRangeOrderConditional.lean`) applies the axiom in, so a later re-weakening (e.g. dropping the
`∃ L₀` threshold back to a bare `∀ L`, or dropping the `2 ≤ L`/`Even L` guards) stops compiling.
-/

namespace LatticeSystem.Tests.ShastrySusceptibilitySubcubicPin

open Matrix LatticeSystem.Quantum

/-- **Signature pin.** `shastry_staggered_susceptibility_subcubic` must keep exactly this shape:
`∀ δ > 0` (not a single fixed constant), `∃ L₀` (not a bare `∀ L`), guarded by `2 ≤ L` and `Even L`,
concluding the resolvent existence and the `≤ δ·L³` (sub-cubic, not linear) susceptibility bound. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 2 ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
      (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
          = (hermitianMinEigenvalue
              (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ) • Φ →
      ∃ y : (Fin L → Fin (N + 1)) → ℂ,
        (heisenbergHamiltonianS (ringCoupling L) N
            - (hermitianMinEigenvalue
                (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ)
              • (1 : ManyBodyOpS (Fin L) N)).mulVec y
          = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ
        ∧ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re
            ≤ δ * (L : ℝ) ^ 3 :=
  shastry_staggered_susceptibility_subcubic N hN

end LatticeSystem.Tests.ShastrySusceptibilitySubcubicPin
