import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Reflection-positivity averaging inequality (Tasaki Lemma 4.5)

This is the abstract combinatorial lemma at the heart of the reflection-positivity proof of the
existence of long-range order (Tasaki §4.1.2, Lemma 4.5, used in the proof of Theorem 4.1).  It is a
purely finite-dimensional statement about a real-valued function `F` of a cyclic string of `2n`
arguments (in Tasaki, `2n` vectors in `ℝ^D`, but the vector structure is never used — the arguments
range over an arbitrary type `V`).

If `F` is invariant under the cyclic shift (cyclicity, eq. (4.1.55)) and satisfies the *reflection
bound* (eq. (4.1.56))
`F(f) ≥ ½ (F(reflect_left f) + F(reflect_right f))`,
where `reflect_left f` mirrors the second half onto the first and `reflect_right f` mirrors the first
half onto the second, then `F` is bounded below by the average of its values on the `2n` constant
strings (eq. (4.1.57)):
`F(f) ≥ (1 / 2n) Σ_j F(j ↦ f j)`.

Tasaki's proof is the elegant "`G_min = 0`" argument: subtract the constant-string average, restrict
to the finite set of strings built from the entries of `f`, and show the minimum is `0` by collapsing
a minimizer to a constant string via repeated use of the reflection bound and cyclicity.  The proof
is elementary but intricate (a doubling induction on the number of leading equal entries); we record
the lemma as a documented axiom and mark it a **finite-dimensional discharge candidate**.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1.2, Lemma 4.5, eqs. (4.1.55)–(4.1.57), pp. 87–88.
-/

namespace LatticeSystem.Math

/-- The **cyclic shift** of a length-`2n` string, `reindexCyclic f = f ∘ finRotate (2n)`
(eq. (4.1.55) acts by this shift).  `finRotate (2n)` is the one-step rotation of `Fin (2n)`. -/
def reindexCyclic {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => f (finRotate (2 * n) i)

/-- The **left reflection** `reflectLeft f = (f_1, …, f_n, f_n, …, f_1)`: keep the first half, and
mirror it onto the second half (eq. (4.1.56), first reflected string).  In `0`-indexed form, entry
`i ≥ n` takes the value `f (2n−1−i) = f i.rev`. -/
def reflectLeft {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => if i.val < n then f i else f i.rev

/-- The **right reflection** `reflectRight f = (f_{2n}, …, f_{n+1}, f_{n+1}, …, f_{2n})`: keep the
second half, and mirror it onto the first half (eq. (4.1.56), second reflected string).  In
`0`-indexed form, entry `i < n` takes the value `f (2n−1−i) = f i.rev`. -/
def reflectRight {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => if i.val < n then f i.rev else f i

/-- **Tasaki Lemma 4.5 (reflection-positivity averaging inequality), AXIOM.**  Let `n ≥ 1` and let
`F : (Fin (2n) → V) → ℝ` be a real-valued function of a cyclic string of `2n` arguments in an
arbitrary type `V`.  Assume `F` is invariant under the cyclic shift (`hcyc`, eq. (4.1.55)) and
satisfies the reflection bound (`hrefl`, eq. (4.1.56)):
`F f ≥ ½ (F (reflectLeft n f) + F (reflectRight n f))` for all `f`.  Then `F` is bounded below by the
average of its values on the `2n` constant strings (eq. (4.1.57)):
`F f ≥ (1 / 2n) Σ_j F (fun _ => f j)`.

The vector structure of the arguments plays no role, so `V` is arbitrary.  Tasaki's proof is
elementary (the `G_min = 0` collapse argument) but intricate; recorded as a documented axiom and a
finite-dimensional discharge candidate. -/
axiom reflectionPositivity_averaging {V : Type*} (n : ℕ) (hn : 1 ≤ n)
    (F : (Fin (2 * n) → V) → ℝ)
    (hcyc : ∀ f, F (reindexCyclic n f) = F f)
    (hrefl : ∀ f, (F (reflectLeft n f) + F (reflectRight n f)) / 2 ≤ F f) :
    ∀ f : Fin (2 * n) → V,
      (∑ j : Fin (2 * n), F (fun _ => f j)) / (2 * n : ℝ) ≤ F f

end LatticeSystem.Math
