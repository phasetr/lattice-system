import LatticeSystem.Quantum.SpinS.CartesianAxis

/-!
# Test coverage for `Quantum/SpinS/CartesianAxis`

Red-first signature pin for the R1 axis-foundation extraction (#5187): this file imports
**only** the new foundation module `LatticeSystem.Quantum.SpinS.CartesianAxis`, not either of
the two Anderson-tower modules the three declarations were relocated from. Pinning the exact
public type and binder shape of `stagOpVec`, `leviCivita3`, `totalSpinSOpVec` this way proves
the foundation stands alone and preserves the namespace (`LatticeSystem.Quantum`) and signatures
verbatim across the move.
-/

namespace LatticeSystem.Tests.CartesianAxis

open LatticeSystem.Quantum

/-- `leviCivita3` is the totally antisymmetric `Fin 3 → Fin 3 → Fin 3 → ℂ` scalar. -/
example : Fin 3 → Fin 3 → Fin 3 → ℂ := leviCivita3

/-- `stagOpVec` takes the staggering pattern `A` and system size `N` explicitly, with the site
type `Λ` implicit, and returns the axis-indexed staggered order operator vector. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ) :
    Fin 3 → ManyBodyOpS Λ N := stagOpVec A N

/-- `totalSpinSOpVec` takes the site type `Λ` explicitly (unlike `stagOpVec`) together with the
system size `N`, and returns the axis-indexed total-spin generator vector. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    Fin 3 → ManyBodyOpS Λ N := totalSpinSOpVec Λ N

end LatticeSystem.Tests.CartesianAxis
