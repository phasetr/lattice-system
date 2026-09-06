import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneral
import LatticeSystem.Quantum.SpinS.OperatorSupport
import LatticeSystem.Math.Combinatorics.SiteBall

/-!
# Signature pin: the ring-ball locality bridge

`Quantum/SpinS/LiebSchultzMattisGeneral.lean` defines the range-`r` window `window L r x` and the
commutant-form locality marker `IsLocalRangeR` against it.  This file pins the lemmas that tie them
to the generic layers: `window_eq_siteBall` and `mem_window`, against the generic metric ball
`siteBall` (`Math/Combinatorics/SiteBall.lean`), and `isLocalRangeR_iff_supportedOnS`, against the
generic support/commutant bridge `supportedOnS_iff_commute_onSiteS`
(`Quantum/SpinS/OperatorSupport.lean`).

`window L r x` *is* `siteBall (ringDist L) r x`, so the site-set identity is definitional and `rfl`
closes it: the pins below measure definitional agreement with the ball, and a filter with a
different orientation breaks a pin here.  The ball filters on `dist y x ≤ r`, hence on
`ringDist L y x ≤ r`, whereas
Tasaki writes the window centred at `x`, `ringDist L x y ≤ r`; the two orders are exchanged by
`ringDist_comm` in `mem_window`, which is the single membership lemma every consumer uses.

The site-set pins catch a transposition written into their own statements: substituting the swapped
wrapper `fun a b => ringDist L b a` for `ringDist L` on the right-hand side makes the fixture fail
to elaborate with a type mismatch, since the window is the ball at `ringDist L` and the wrapper is
not that up to unfolding; a wrong centre, a wrong radius, and an unrelated distance function fail
the same way.  The membership pin fixes the centred argument order: stating it as
`ringDist L y x ≤ r` — the same set, by `ringDist_comm` — is rejected, because only the *term*
`mem_window`, whose type carries the centred order, is offered as its proof.

The locality pin holds `IsLocalRangeR`'s commutant condition, spelled out rather than named so the
fixture exercises the site set independently of the predicate's own definition, equivalent to
support on the window via `supportedOnS_iff_commute_onSiteS` composed with a membership lemma for
`window`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162 (the range-`r` window `W_x`, eq. (6.2.26)); §7.1.3, p. 191
(`IsAKLTPerturbation`'s locality hypothesis, sharing the same predicate).
-/

namespace LatticeSystem.Tests.RingBallLocalityBridgePin

open Matrix LatticeSystem.Quantum LatticeSystem.Math

/-! ## Site-set pin: `window` is `siteBall` at `ringDist L` -/

/-- **Site-set pin.** The range-`r` window around `x` is the metric ball of radius `r` around `x`
for the ring distance. -/
example {L r : ℕ} {x : Fin L} :
    window L r x = siteBall (ringDist L) r x :=
  window_eq_siteBall

/-! ## Locality pin: `IsLocalRangeR`'s condition, written out -/

/-- **Locality pin.** Commuting with every single-site operator seated strictly farther than `r`
from `x` is exactly support on the window `window L r x`. -/
example {L N r : ℕ} {x : Fin L} {op : ManyBodyOpS (Fin L) N} :
    (∀ y : Fin L, r < ringDist L x y →
        ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS y A))
      ↔ SupportedOnS (window L r x) op :=
  isLocalRangeR_iff_supportedOnS

/-! ## Definitional pin and membership order -/

/-- **Definitional pin.** `window L r x` is *defined as* `siteBall (ringDist L) r x`, not merely
equal to it up to a proved identity, so `rfl` closes the site-set equation: the pin measures
definitional agreement with `siteBall (ringDist L) r x`, and a definition with the opposite
orientation of the ring distance fails it, though it does not detect an equivalent filter written
elsewhere. -/
example {L r : ℕ} {x : Fin L} :
    window L r x = siteBall (ringDist L) r x :=
  rfl

/-- **Membership-order pin.** Membership in the window is Tasaki's centred distance bound
`ringDist L x y ≤ r` (§6.2, eq. (6.2.26)), with `x` in the first slot: `mem_window` is where the
ball's opposite order is exchanged, so its type is what fixes the order for every consumer. -/
example {L r : ℕ} {x y : Fin L} :
    y ∈ window L r x ↔ ringDist L x y ≤ r :=
  mem_window

end LatticeSystem.Tests.RingBallLocalityBridgePin
