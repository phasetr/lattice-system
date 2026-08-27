import LatticeSystem.Quantum.TimeReversalSpinHalf

/-!
# Test coverage for Tasaki Problem 2.3.a (`inner_timeReversal_eq_zero_of_sq_neg`)

Signature pin for the capstone `inner_timeReversal_eq_zero_of_sq_neg` in
`LatticeSystem/Quantum/TimeReversalSpinHalf.lean` (Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, Problem 2.3.a, p. 31, solution p. 496, Appendix A.4.3
eq. (A.4.17)): for any map `V` on an inner product space that reverses the inner product
(`⟨V u, V v⟩ = ⟨v, u⟩`) and is an involution up to sign (`V (V v) = -v`), every vector is
orthogonal to its image, `⟨v, V v⟩ = 0`; no linearity assumption on `V` is needed. The
fixture fixes the capstone's exact name, binder order and hypothesis shapes by applying it
to discharge abstract witness data `(E, V, hanti, hsq)`.
-/

namespace LatticeSystem.Tests.Problem23a

open LatticeSystem.Quantum

/-- Any map `V` on an inner product space `E` that reverses the inner product
(`⟨V u, V v⟩ = ⟨v, u⟩`) and is an involution up to sign (`V (V v) = -v`) sends every
vector to something orthogonal to it: `⟨v, V v⟩ = 0`. This pins the exact name, binder
order, and hypothesis shapes of `inner_timeReversal_eq_zero_of_sq_neg`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : E → E)
    (hanti : ∀ u v, inner ℂ (V u) (V v) = inner ℂ v u)
    (hsq : ∀ v, V (V v) = -v)
    (v : E) :
    inner ℂ v (V v) = 0 :=
  inner_timeReversal_eq_zero_of_sq_neg V hanti hsq v

end LatticeSystem.Tests.Problem23a
