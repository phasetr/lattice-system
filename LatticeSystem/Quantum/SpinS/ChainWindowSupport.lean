import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# The chain window `[a, b]` as a site set, and support on it

Locality of an operator on an open chain `Fin L`, confined to a fixed window `[a, b]`, expressed
through the general support predicate `SupportedOnS` (`Quantum/SpinS/OperatorSupport.lean`) rather
than through a window-specific predicate.  `chainWindow L a b` is the site set, and
`supportedOnS_chainWindow_iff` identifies support on it with the commutant condition that the
operator commutes with every single-site operator seated at an index below `a` or above `b`.

The endpoints are plain naturals compared against `z.val : ℕ`, so the window truncates at `L - 1`
instead of wrapping, which is what a window on an open chain means.  Reading them as sites of
`Fin L` instead — `Finset.Icc (a : Fin L) (b : Fin L)` — does not give this truncated window: at
`L = 5`, `a = 3`, `b = 7` the endpoint `b` comes out as `2` and that interval is empty, where this
window is `{3, 4}`.  In the default scope that spelling does not elaborate.

Repository-internal material with **no textbook source**: the window is a combinatorial site set
carrying no spin content.  It has two consumers: Tasaki Proposition 8.4
(`Quantum/SpinS/KennedyTasakiProp84.lean`), whose locality hypothesis is stated with it, and the
signature pin `LatticeSystem/Tests/ChainWindowSupportPin.lean`.
`Quantum/SpinS/LiebSchultzMattisDiscrete.lean` names it in a doc comment without importing this
module, so that mention is a cross-reference and not a consumer.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- The **chain window** `[a, b]` as a site set of `Fin L`: the sites `z` with `a ≤ z.val ≤ b`.
The endpoints are naturals compared against `z.val`, so the set truncates at `L - 1` rather than
wrapping, and it is empty exactly when `b < a` or `L ≤ a`. -/
def chainWindow (L a b : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun z => a ≤ z.val ∧ z.val ≤ b

/-- Membership in the chain window is the pair of index bounds. -/
theorem mem_chainWindow {L a b : ℕ} {z : Fin L} :
    z ∈ chainWindow L a b ↔ a ≤ z.val ∧ z.val ≤ b := by
  simp [chainWindow]

/-- Non-membership in the chain window is the disjunction that names a site strictly outside
`[a, b]`; this is the form a locality argument consumes. -/
theorem notMem_chainWindow {L a b : ℕ} {z : Fin L} :
    z ∉ chainWindow L a b ↔ (z.val < a ∨ b < z.val) := by
  constructor
  · intro h
    by_contra hc
    exact h (mem_chainWindow.mpr (by omega))
  · intro h hmem
    have := mem_chainWindow.mp hmem
    omega

/-- **Window locality is support on the window.**  An operator is supported on the chain window
`[a, b]` exactly when it commutes with every single-site operator seated at an index below `a` or
above `b`.  This is `supportedOnS_iff_commute_onSiteS` transported along `notMem_chainWindow`, so
it holds for every `L`, `a` and `b`: no `a ≤ b`, no interior margin, and no relation between the
endpoints and `L` is needed, and the degenerate parameters are covered — at `b < a` both sides say
the operator is central, and at `b ≥ L` the right-hand disjunction collapses to `z.val < a`, the
truncation that separates this window from a mod-`L` reading of its endpoints (module header). -/
theorem supportedOnS_chainWindow_iff {L a b : ℕ} {op : ManyBodyOpS (Fin L) N} :
    SupportedOnS (chainWindow L a b) op ↔
      ∀ z : Fin L, (z.val < a ∨ b < z.val) →
        ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS z A) := by
  rw [supportedOnS_iff_commute_onSiteS]
  exact forall_congr' fun z => imp_congr_left notMem_chainWindow

end LatticeSystem.Quantum
