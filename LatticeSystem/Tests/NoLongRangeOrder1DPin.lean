import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D

/-!
# Signature pins: `no_long_range_order_1d` and the `hsusc` guard shape

Tasaki §4.1 Corollary 4.3 (PR #5414, the `shastry_staggered_susceptibility_bound` →
`shastry_staggered_susceptibility_subcubic` rename). Two independent pins:

1. `no_long_range_order_1d` itself must **not change** across this rename: it is written out here
   in full, independently of `no_long_range_order_1d_of_susceptibility`, so an added hypothesis, an
   altered quantifier order, or `Even L` drift breaks this file even though the internal axiom the
   theorem rests on changed.
2. `no_long_range_order_1d_of_susceptibility`'s `hsusc` hypothesis binder is pinned in the exact
   shape the new axiom must supply: `∀ δ > 0, ∃ L₀, ∀ L, L₀ ≤ L → 2 ≤ L → Even L → …`. This
   double-pins the `∃ L₀` threshold (a bare `∀ L` is a strictly stronger, false statement — see
   the module doc of `ShastrySusceptibilitySubcubicPin.lean`) and the `2 ≤ L`/`Even L` guards
   (odd and degenerate ring sizes are excluded, both here and at the axiom).
-/

namespace LatticeSystem.Tests.NoLongRangeOrder1DPin

open Matrix LatticeSystem.Quantum

/-- **Signature pin: `no_long_range_order_1d`.** Written out independently of the conditional
reduction it is discharged from, so the theorem's own public statement is pinned regardless of how
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

/-- **Signature pin, `hsusc` guard shape.** `no_long_range_order_1d_of_susceptibility`'s
susceptibility hypothesis must keep the `∀ δ > 0, ∃ L₀` threshold structure and the `2 ≤ L`/
`Even L` guards: an argument of any weaker shape (e.g. a bare `∀ L` with no threshold, or dropping
either guard) fails to elaborate against this pinned binder type. -/
example (N : ℕ) (hN : 1 ≤ N)
    (hsusc : ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 2 ≤ L → Even L →
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
            ≤ δ * (L : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)|
          < ε :=
  no_long_range_order_1d_of_susceptibility N hN hsusc

end LatticeSystem.Tests.NoLongRangeOrder1DPin
