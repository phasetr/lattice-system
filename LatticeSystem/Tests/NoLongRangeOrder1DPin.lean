import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D

/-!
# Signature pin: `no_long_range_order_1d`

`no_long_range_order_1d` is written out here in full, independently of the conditional route
`no_long_range_order_1d_of_theorem_4_2` it is derived from.  The theorem's own `ε`–`δ` statement is
what consumers see, so it is fixed on its own: an added hypothesis, an altered quantifier order or
`Even L` drift breaks this file even when the unproved input its proof consumes is exchanged for
another one — as it was when the susceptibility route was replaced by Tasaki's own contraposition
from Theorem 4.2.
-/

namespace LatticeSystem.Tests.NoLongRangeOrder1DPin

open Matrix LatticeSystem.Quantum

/-- **Signature pin: `no_long_range_order_1d`.** Written out independently of the conditional
reduction it is derived from, so the theorem's own public statement is pinned regardless of how
its proof (or the axiom it rests on) changes. -/
example (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)| < ε :=
  no_long_range_order_1d N

end LatticeSystem.Tests.NoLongRangeOrder1DPin
