import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D
import LatticeSystem.Quantum.SpinS.ShastryNoSSBReduction

/-!
# Signature pin: Tasaki's own route to Corollary 4.3 (contraposition, p. 77)

One pin for the contraposition route, the route that replaced the earlier reduction through a
staggered-susceptibility axiom of the corollary's own:
`no_long_range_order_1d_of_theorem_4_2` — the signature the proof of `no_long_range_order_1d`
applies, at `N` with `hN : 1 ≤ N` (the `N = 0` case is its own unconditional branch).  Its
hypothesis is Theorem 4.2's conclusion **applied**, via `shastry_no_symmetry_breaking_1d N`,
rather than retyped as a binder: any drift between what this pin supplies and what the
declaration demands surfaces as an application-elaboration error against the *existing*
declaration `shastry_no_symmetry_breaking_1d`, not as two independently-transcribed types that
could silently diverge.  `no_long_range_order_1d` itself is pinned once, in
`NoLongRangeOrder1DPin.lean`; the result type appearing here is Tasaki's third sentence alone,
his `α = 3` instance (Lean axis `2`), which the capstone extends to all three axes by SU(2)
invariance.

**Boundary conditions not pinned here, and why.**  The route additionally needs `2 ≤ L` (to invoke
`afm_ring_ground_state_data`, whose four guards are `Even L`, `2 ≤ L`, `1 ≤ N`, and a nonempty
carrier) and needs the `N = 0` case to require no axiom at all.  Neither survives as a top-level
hypothesis or a separate conclusion of `no_long_range_order_1d`'s own *type*: `2 ≤ L` is absorbed
into the `∃ L₀` threshold, and "needs no axiom" is a `#print axioms` fact about a proof term, not a
proposition any `example : T := e` can fail to elaborate against.  Pinning either by writing a
*weaker* type that happens to compile would defeat the purpose; the honest record is that they are
not expressible as compile-fail fixtures at this signature level, and that the pin site of `2 ≤ L`
is `Even L` alone, which the pin's conclusion already carries.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3, p. 77 (proof: contraposition against Theorem 3.2, p. 70, and
Theorem 4.2, p. 76); §3.4, Theorem 3.2, eqs. (3.4.21)-(3.4.22), p. 70.
-/

namespace LatticeSystem.Tests.Corollary43ContrapositionPin

open Matrix LatticeSystem.Quantum

/-- **Signature pin for the contraposition theorem.**  Applies Theorem 4.2's conclusion
(`shastry_no_symmetry_breaking_1d N`) to `no_long_range_order_1d_of_theorem_4_2`, at the `α = 3`
conclusion type Tasaki's third sentence yields — the Lean axis-`2` instance of what
`no_long_range_order_1d` carries for `N ≥ 1`.  The hypothesis is supplied by application rather
than retyped, so a drift in either declaration breaks this fixture at elaboration instead of
leaving two transcriptions to diverge silently. -/
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

end LatticeSystem.Tests.Corollary43ContrapositionPin
