import Mathlib.Data.Fin.Basic

/-!
# Ring distance on `Fin L`

The cyclic (periodic-boundary) distance between two sites of the ring `Fin L`.  A lightweight
combinatorial helper with no operator-algebra dependencies, factored into its own module so that the
locality predicate `IsLocalRangeR` (Tasaki §6.2) and the hidden-antiferromagnetic-order correlation
decay estimates (Tasaki §6.3) can share the single definition without a build-layer inversion.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, §6.3.
-/

namespace LatticeSystem.Quantum

/-- The **ring distance** between sites `x, y` on `Fin L`: the shorter of the two cyclic arc lengths
`(y − x) mod L` and `(x − y) mod L`. -/
def ringDist (L : ℕ) (x y : Fin L) : ℕ :=
  min ((y.val + L - x.val) % L) ((x.val + L - y.val) % L)

end LatticeSystem.Quantum
