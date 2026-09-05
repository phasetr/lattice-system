import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneral
import LatticeSystem.Quantum.SpinS.OperatorSupport
import LatticeSystem.Math.Combinatorics.SiteBall

/-!
# Signature pin: the ring-ball locality bridge

`Quantum/SpinS/LiebSchultzMattisGeneral.lean` defines the range-`r` window `window L r x` and the
commutant-form locality marker `IsLocalRangeR` against it.  This file pins the two lemmas that tie
them to the generic layers: `window_eq_siteBall`, against the generic metric ball `siteBall`
(`Math/Combinatorics/SiteBall.lean`), and `isLocalRangeR_iff_supportedOnS`, against the generic
support/commutant bridge `supportedOnS_iff_commute_onSiteS`
(`Quantum/SpinS/OperatorSupport.lean`).

`window L r x` filters on `ringDist L x y ≤ r`; `siteBall dist r x` filters on `dist y x ≤ r`, so
instantiating `dist := ringDist L` gives `ringDist L y x ≤ r` — the two predicates put `x` and `y`
into `ringDist` in opposite orders. They still cut out the same Finset, because `ringDist_comm`
proves `ringDist` is symmetric for every pair, not just this one, but the equality is not
definitional: `rfl` does not close `window L r x = siteBall (ringDist L) r x`, and
`window_eq_siteBall` rewrites the filter predicate through `ringDist_comm` instead.

The site-set pin's reach against a transposed argument order stops at the definition boundary. A
transposition in the pin's own statement is caught: substituting the swapped wrapper
`fun a b => ringDist L b a` for `ringDist L` on the right-hand side makes the fixture fail to
elaborate with a type mismatch, since `window_eq_siteBall` is stated at `ringDist L` and the wrapper
is not that up to unfolding; a wrong centre, a wrong radius, and an unrelated distance function fail
the same way. A transposition inside the definition of `window` or of `siteBall` is not caught:
either one makes the two filter predicates syntactically identical, so the equality becomes
definitional — `rfl` closes it — and the pin passes unchanged.

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

end LatticeSystem.Tests.RingBallLocalityBridgePin
