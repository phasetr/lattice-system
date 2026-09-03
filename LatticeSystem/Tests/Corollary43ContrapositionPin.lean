import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D
import LatticeSystem.Quantum.SpinS.ShastryNoSSBReduction

/-!
# Red: Tasaki's own route to Corollary 4.3 (contraposition, p. 77), not yet implemented

Two independent pins for PR-2 (issue #5416), fixed **before** the new conditional theorem exists:

1. `no_long_range_order_1d_of_theorem_4_2` — the signature the reproof of `no_long_range_order_1d`
   will apply, at `N` with `hN : 1 ≤ N` (the `N = 0` case stays its own unconditional branch, as
   today).  Its hypothesis is Theorem 4.2's conclusion **applied**, via
   `shastry_no_symmetry_breaking_1d N`, rather than retyped as a binder: any drift between what
   this pin supplies and what the real declaration demands surfaces as an application-elaboration
   error against the *existing* declaration `shastry_no_symmetry_breaking_1d`, not as two
   independently-transcribed types that could silently diverge.  This identifier does not exist
   yet, so this pin is Red.
2. `no_long_range_order_1d`'s own statement, written out independently of pin 1 and of the
   existing `NoLongRangeOrder1DPin.lean` (which pins it alongside the doomed
   `no_long_range_order_1d_of_susceptibility`, a declaration this issue's scope deletes): even if
   implementing PR-2 removes or rewrites that file, this copy keeps checking the untouched
   `no_long_range_order_1d`.  This identifier already exists, so this pin is Green today; it turns
   Red only if the statement drifts during implementation.

**Boundary conditions not pinned here, and why.**  The route additionally needs `2 ≤ L` (to invoke
`afm_ring_ground_state_data`, whose four guards are `Even L`, `2 ≤ L`, `1 ≤ N`, and a nonempty
carrier) and needs the `N = 0` case to require no axiom at all.  Neither survives as a top-level
hypothesis or a separate conclusion of `no_long_range_order_1d`'s own *type*: `2 ≤ L` is absorbed
into the `∃ L₀` threshold exactly as it is in the already-deleted-in-scope
`no_long_range_order_1d_of_susceptibility` (`refine ⟨max L₀ 2, …⟩` there), and "needs no axiom" is
a `#print axioms` fact about a proof term, not a proposition any `example : T := e` can fail to
elaborate against.  Pinning either by writing a *weaker* type that happens to compile would be
exactly the trap this module's own author has been warned against twice; the honest report is that
they are not expressible as compile-fail fixtures at this signature level; the pin site of `2 ≤ L`
is `Even L` alone, which pin 1's conclusion already carries.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3, p. 77 (proof: contraposition against Theorem 3.2, p. 70, and
Theorem 4.2, p. 76); §3.4, Theorem 3.2, eqs. (3.4.21)-(3.4.22), pp. 69-70.
-/

namespace LatticeSystem.Tests.Corollary43ContrapositionPin

open Matrix LatticeSystem.Quantum

/-- **Red: signature pin for the not-yet-existing contraposition theorem.**  Applies Theorem 4.2's
conclusion (`shastry_no_symmetry_breaking_1d N`) to the not-yet-existing
`no_long_range_order_1d_of_theorem_4_2`, at the exact conclusion type `no_long_range_order_1d`
carries for `N ≥ 1`.  Fails today with `unknown identifier` on the new theorem's name alone: the
hypothesis term elaborates fine against the existing `shastry_no_symmetry_breaking_1d`, isolating
the failure to the one identifier PR-2 has to add. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)|
          < ε :=
  no_long_range_order_1d_of_theorem_4_2 N hN (shastry_no_symmetry_breaking_1d N)

/-- **Regression guard, independent of `NoLongRangeOrder1DPin.lean`: `no_long_range_order_1d`'s
statement.**  Written out on its own so that this file keeps checking it even if the existing pin
file is touched or deleted alongside `no_long_range_order_1d_of_susceptibility` during PR-2.
Compiles today (the statement is, as required, unchanged); it is a drift guard, not a Red. -/
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

end LatticeSystem.Tests.Corollary43ContrapositionPin
