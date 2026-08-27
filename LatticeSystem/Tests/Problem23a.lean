import LatticeSystem.Quantum.TimeReversalSpinHalf

/-!
# Test coverage for Tasaki Problem 2.3.a (`inner_timeReversal_eq_zero_of_sq_neg`)

Red-first signature pin for `TSK-001` (Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, Problem 2.3.a, p. 31, solution p. 496, Appendix A.4.3
eq. (A.4.17)): for any antiunitary-antilinear involution-up-to-sign `V` on an inner
product space (`⟨V u, V v⟩ = ⟨v, u⟩` and `V (V v) = -v`), every vector is orthogonal
to its image, `⟨v, V v⟩ = 0`. This file consumes the not-yet-implemented capstone
`inner_timeReversal_eq_zero_of_sq_neg` (to be added in
`LatticeSystem/Quantum/TimeReversalSpinHalf.lean` immediately after
`timeReversalSpinHalf_sq`) by its exact name and signature, applying it to abstract
witness data `(E, V, hanti, hsq)` via `exact`.
-/

namespace LatticeSystem.Tests.Problem23a

open LatticeSystem.Quantum

/-- Any antiunitary-antilinear involution-up-to-sign `V` on an inner product space `E`
sends every vector to something orthogonal to it: `⟨v, V v⟩ = 0`. This pins the exact
name, binder order, and hypothesis shapes of `inner_timeReversal_eq_zero_of_sq_neg`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : E → E)
    (hanti : ∀ u v, inner ℂ (V u) (V v) = inner ℂ v u)
    (hsq : ∀ v, V (V v) = -v)
    (v : E) :
    inner ℂ v (V v) = 0 :=
  inner_timeReversal_eq_zero_of_sq_neg V hanti hsq v

end LatticeSystem.Tests.Problem23a
