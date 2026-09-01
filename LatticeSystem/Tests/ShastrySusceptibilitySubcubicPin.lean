import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D

/-!
# Signature pin: `shastry_staggered_susceptibility_subcubic`

This file pins the quantifier structure of the documented axiom
`shastry_staggered_susceptibility_subcubic` (Tasaki §4.1, toward Corollary 4.3) in exactly the
shape its sole consumer `no_long_range_order_1d_of_susceptibility`
(`NoLongRangeOrderConditional.lean`) applies it in.  Every part of that shape carries a soundness
obligation, so a re-weakening must stop compiling here rather than pass unnoticed:

* the margin `∀ δ > 0` cannot be traded for one size-uniform constant with a linear bound
  (`∃ C ≥ 0, ∀ L, χ ≤ C·L`): at odd `N` the correlation asymptotics force `χ ≳ L (log L)³`, hence
  `χ/L → ∞`, so that stronger form is false;
* the `∃ L₀` threshold cannot be dropped for a bare `∀ L`: the two-site ring `N = 1`, `L = 2` has
  `χ = 1/2` against `δ·2³`, refuting every `δ < 1/16`;
* the `2 ≤ L` and `Even L` guards cannot be dropped: only bipartite rings carry a balanced
  staggered sublattice, and odd or degenerate ring sizes lie outside Tasaki's §4.1 setting.
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
