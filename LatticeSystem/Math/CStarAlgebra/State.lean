import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Matrix.Order

/-!
# Tasaki Appendix A.7: states on the quasi-local algebra (Definition A.23, Theorem A.24)

Tasaki's operator-algebraic formulation of infinite quantum systems characterizes the physical
state of an (infinite) system by the expectation values of the *quasi-local* observables `A` (a
unital C*-algebra).

* **Definition A.23** — a *state* `ρ(·)` is a (continuous) linear functional on `A` with `ρ(1̂) = 1`
  and `ρ(Â† Â) ≥ 0` for every `Â ∈ A` (positivity).  It follows that `|ρ(Â)| ≤ ‖Â‖`.
* **Theorem A.24 (Banach–Alaoglu)** — the set of all states on `A` is compact in the weak-∗
  topology.  Concretely: any sequence of states has a weak-∗ convergent subsequence (eq. (A.7.3)),
  which is what makes infinite-volume limits of states available.

We work over an abstract unital complex C*-algebra `A` (mathlib's `CStarAlgebra` typeclass), with
the weak-∗ topology supplied by `WeakDual ℂ A`.  Definition A.23 is a genuine `def`; the
compactness Theorem A.24 (Banach–Alaoglu, a deep functional-analytic result) is recorded as a
documented axiom, consistent with the axiomatize-first treatment of this appendix.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.7, Definition A.23 and Theorem A.24, eqs. (A.7.2)–(A.7.3), pp. 488–489.
-/

namespace LatticeSystem.Math

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- **Tasaki Definition A.23 (state on a C*-algebra).**  A *state* on a unital complex C*-algebra
`A` is a weak-∗-continuous linear functional `φ` (an element of `WeakDual ℂ A`) that is normalized,
`φ(1) = 1`, and positive, `0 ≤ φ(Â† Â)` for every `Â ∈ A`.  The value `φ(Â)` is the expectation of
the observable `Â` in the state `φ`. -/
def IsState (φ : WeakDual ℂ A) : Prop :=
  φ 1 = 1 ∧ ∀ a : A, 0 ≤ φ (star a * a)

/-- The set of all states on `A`, as a subset of the weak-∗ dual `WeakDual ℂ A`. -/
def stateSpace (A : Type*) [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A] :
    Set (WeakDual ℂ A) :=
  {φ | IsState φ}

/-- **Tasaki Theorem A.24 (Banach–Alaoglu for states), AXIOM.**  The set of all states on a unital
complex C*-algebra `A` is compact in the weak-∗ topology (eq. (A.7.3): every sequence of states has
a weak-∗ convergent subsequence, with limit again a state).  This is the operator-algebraic input
that makes infinite-volume limits of states available; recorded as a documented axiom. -/
axiom stateSpace_isCompact (A : Type*) [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A] :
    IsCompact (stateSpace A)

end LatticeSystem.Math
