import LatticeSystem.Quantum.SpinS.KennedyTasakiProp84
import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the chain window `[a, b]` and Proposition 8.4's locality hypothesis

`Quantum/SpinS/KennedyTasakiProp84.lean` states Tasaki Proposition 8.4's locality hypothesis as
support on the site set `chainWindow L a b`. The window is filtered on the `ℕ`-valued index, so
it truncates at `L - 1` rather than wrapping.

Proposition 8.4's own proof does not detect a wrong window. The locality condition is the
left-hand side of a biconditional: the necessity direction consumes it and the sufficiency
direction produces it, and the necessity direction only ever instantiates it at the two probe
sites `0` and `b + 1`. Agreement at those two indices is not enough on its own, though: that
proof accepts a set `W` in place of the window exactly when `W` omits both probe sites and
contains every site with `a ≤ z.val ≤ b`. `[a + 1, b]` omits both probes, so the necessity
direction accepts it, and it is the sufficiency direction that rejects it, at `z.val = a`. This
pin is the guard: it writes the outside-window condition out verbatim and holds it equivalent to
support on the window, so the equivalence is proved through a lemma that must hold of whatever
`chainWindow` is defined to be, and the pinned disjunction determines the set.

The second pin holds Proposition 8.4's restated statement.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2–§8.2.3, Proposition 8.4, p. 250.
-/

namespace LatticeSystem.Tests.ChainWindowSupportPin

open Matrix LatticeSystem.Quantum

/-! ## Window pin: the outside-window condition, written out -/

/-- **Window pin.** Support on `chainWindow L a b` is exactly the condition that the operator
commutes with every single-site operator seated at an index below `a` or above `b`. -/
example {L N a b : ℕ} {op : ManyBodyOpS (Fin L) N} :
    (∀ z : Fin L, (z.val < a ∨ b < z.val) →
        ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS z A))
      ↔ SupportedOnS (chainWindow L a b) op :=
  supportedOnS_chainWindow_iff.symm

/-! ## Statement pin: Proposition 8.4 -/

/-- **Statement pin.** The hypotheses and both conjuncts of `tasaki_prop_8_4_local_monomial`,
held against silent drift. -/
example {L : ℕ} (w : List (Fin L × Fin 3)) (a b : ℕ)
    (hw : ∀ p ∈ w, a ≤ (p.1 : Fin L).val ∧ (p.1 : Fin L).val ≤ b)
    (hleft : 0 < a) (hright : b + 1 < L) :
    (SupportedOnS (chainWindow L a b) (ktUnitaryS L * spinMonomialS w * ktUnitaryS L)
        ↔ IsZ2Z2Invariant (spinMonomialS w))
      ∧ (IsZ2Z2Invariant (spinMonomialS w) →
          IsZ2Z2Invariant (ktUnitaryS L * spinMonomialS w * ktUnitaryS L)) :=
  tasaki_prop_8_4_local_monomial w a b hw hleft hright

end LatticeSystem.Tests.ChainWindowSupportPin
