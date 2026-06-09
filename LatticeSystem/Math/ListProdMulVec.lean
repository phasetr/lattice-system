import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Ordered operator products acting on a `mulVec`-invariant submodule

A small generic lemma: if a submodule `p` of `n → R` is invariant under `Matrix.mulVec` by each
operator appearing in a list `l`, then the ordered product `(l.prod).mulVec v` stays in `p` whenever
`v ∈ p`.  This is the span-closure tool behind the Fock-space factorisation arguments (a vector
built by an ordered product of operators, each a finite sum of "elementary" operators that keep a
span of monomials invariant, lands in that span).
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **Ordered product on an invariant submodule.**  If `p` is closed under `mulVec` by every
operator in the list `l`, then `(l.prod).mulVec v ∈ p` for every `v ∈ p`.  Proof by induction on
`l`, peeling
the leftmost factor via `Matrix.mulVec_mulVec`. -/
theorem listProd_mulVec_mem {l : List (Matrix n n R)} {p : Submodule R (n → R)}
    (hclosed : ∀ M ∈ l, ∀ w ∈ p, M.mulVec w ∈ p) {v : n → R} (hv : v ∈ p) :
    (l.prod).mulVec v ∈ p := by
  induction l with
  | nil => simpa using hv
  | cons M rest ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec]
    exact hclosed M (List.mem_cons.mpr (Or.inl rfl)) _
      (ih (fun N hN => hclosed N (List.mem_cons.mpr (Or.inr hN))))

end LatticeSystem.Math
