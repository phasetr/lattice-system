import LatticeSystem.Quantum.SpinS.InfiniteVolumeGroundState
import LatticeSystem.Math.CStarAlgebra.GroundState

/-!
# Tasaki §7.1: the AKLT model on the infinite chain (Theorem 7.2, Matsui)

The finite-volume AKLT theorem (Theorem 7.1) gives a unique gapped ground state for every chain
length.  Passing to the infinite chain `ℤ`, the model is treated through the quasi-local
`C*`-algebra of observables, where a *ground state* and a *nonzero gap* are defined operator-
algebraically (Tasaki Definitions A.25 and A.27): a state `ω` is a ground state iff
`ω(Â† [Ĥ, Â]) ≥ 0` for every local `Â` (`IsGroundState`), and it has a nonzero gap iff
`ω(Â† [Ĥ, Â]) ≥ γ ω(Â† Â)` for some `γ > 0` whenever `ω(Â) = 0` (`HasNonzeroGap`).

**Theorem 7.2** (Matsui): the AKLT model on the infinite chain has a **unique** ground state
accompanied by a **nonzero gap** (in the sense of Definitions A.25/A.27).  The unique
infinite-volume
ground state is the proper `L↑∞` limit of the finite-volume VBS state.  Affleck–Kennedy–Lieb–Tasaki
[5] proved uniqueness within translation-invariant states; Matsui [53] strengthened it to full
uniqueness, fully characterizing the infinite-chain ground state.

This is a deep operator-algebraic result on the quasi-local `C*`-algebra; per the project policy
such
`C*`-algebraic / `GNS` statements are recorded as faithful, sound **documented axioms**.  The AKLT
infinite-chain dynamics is tied to its spin system through the (uninterpreted) marker
`IsAKLTChainDynamics` — a faithful definition would need the full quasi-local AKLT interaction, so
the
marker keeps the theorem applicable only to genuine AKLT data (not to an arbitrary dynamics).
Uniqueness is asserted among *states* (not arbitrary functionals).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3, Theorem 7.2, p. 179, and Appendix A.7 (Definitions A.25/A.27); I. Affleck, T.
Kennedy,
E. Lieb, H. Tasaki, Commun. Math. Phys. **115**, 477 (1988); T. Matsui, Commun. Math. Phys. **218**,
393 (2001).
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math

variable {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- **The AKLT infinite-chain dynamics marker** `IsAKLTChainDynamics S δ`: the dynamics `δ : A → A`
(`Â ↦ [Ĥ_AKLT, Â]`) is the commutator with the AKLT Hamiltonian on the one-dimensional infinite spin
system `S`.  A faithful definition needs the full quasi-local AKLT interaction `Σ_x ĥ_x^{AKLT}`;
it is
kept as an uninterpreted predicate so that Theorem 7.2 is stated only for genuine AKLT data (and
cannot be applied to an unrelated dynamics on an unrelated spin chain). -/
axiom IsAKLTChainDynamics (S : InfiniteSpinSystem 1 A) (δ : A → A) : Prop

/-- **Tasaki Theorem 7.2 (the AKLT model on the infinite chain, Matsui), AXIOM.**  The AKLT model on
the one-dimensional infinite chain (`InfiniteSpinSystem 1 A`, with the AKLT dynamics `δ` marked by
`IsAKLTChainDynamics`) has a **unique ground state** `ω` — unique *among states* — that is
accompanied
by a **nonzero energy gap**: there is `ω` with `IsState ω`, `IsGroundState ω δ`, every state ground
state equal to `ω`, and a `γ > 0` with `HasNonzeroGap ω δ γ` (Definitions A.25/A.27).

This is the infinite-volume counterpart of Theorem 7.1; the unique ground state is the `L↑∞` limit
of
the VBS state.  Proved by Matsui [53] (uniqueness) building on Affleck–Kennedy–Lieb–Tasaki [5];
recorded as a documented axiom (a deep operator-algebraic / `C*`-result). -/
axiom aklt_theorem_7_2 (S : InfiniteSpinSystem 1 A) (δ : A → A) (hδ : IsAKLTChainDynamics S δ) :
    ∃ ω : WeakDual ℂ A, IsState ω ∧ IsGroundState ω δ ∧
      (∀ ω' : WeakDual ℂ A, IsState ω' → IsGroundState ω' δ → ω' = ω) ∧
      ∃ γ : ℝ, HasNonzeroGap ω δ γ

end LatticeSystem.Quantum
