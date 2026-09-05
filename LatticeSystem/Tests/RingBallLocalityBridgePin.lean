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
definitional: `rfl` does not close `window L r x = siteBall (ringDist L) r x` after unfolding both
sides, only a filter-predicate rewrite through `ringDist_comm` does. That same symmetry is why this
equality pin cannot be used to catch a transposed argument order: substituting a
deliberately-swapped wrapper `fun a b => ringDist L b a` for `ringDist L` on the right-hand side
still discharges the identical equality (by `simp` alone, with no appeal to `ringDist_comm` at all,
because the wrapper's swap cancels against `siteBall`'s own built-in `dist y x` order and lands back
on `ringDist L x y`), and evaluating both filter predicates at a concrete pair with `x ≠ y` agrees
for the same reason. No proposition built only from `ringDist` can separate the two orders, because
they denote the same relation at every pair; the site-set pin below is only a guard against choosing
the wrong `L`, `r`, `x`, or distance function, not against a transposed argument order, which does
not exist as a distinguishable defect here.

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
