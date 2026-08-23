import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Coordinate-block ground-state transport

Two model-independent facts about a Hermitian matrix that is *supported on a coordinate block*:
one relating its unique-ground-state predicate on that block to the same predicate for the block's
submatrix on the whole restricted space, and one identifying the kernel of a diagonal matrix with
the coordinate span of the indices where it vanishes.

Both facts are the generic transport layer needed whenever a Hamiltonian is known to vanish outside
a coordinate subspace (e.g. a projection built from a diagonal indicator): rather than reproving
ground-state uniqueness or a kernel computation for each concrete model, a model only has to supply
the block-support hypothesis (`H = P̂ H P̂`) or the vanishing-locus characterization of a diagonal
matrix's entries, and these two lemmas transport it.

## Main results

* `coordinateSpan` — the subspace of `EuclideanSpace ℂ n` spanned by the standard basis vectors at
  indices satisfying a decidable predicate `P`.
* `coordinateRestrict` — the restriction of a vector of `EuclideanSpace ℂ n` to the coordinates
  satisfying `P`, landing in `EuclideanSpace ℂ {i // P i}`.
* `isUniqueGroundStateOn_coordinateSpan_iff_submatrix` — for `H` supported on the coordinate block
  of `P` (`H = P̂ · H · P̂`, `P̂` the diagonal indicator of `P`), `H`'s unique ground state on the
  coordinate span of `P` at a candidate `φ` is equivalent to the submatrix restriction of `H` to
  that block having the restricted candidate as its unique ground state on the whole restricted
  space.
* `matrixKernel_diagonal_eq_coordinateSpan` — the kernel of a diagonal matrix equals the coordinate
  span of the predicate characterizing its zero entries.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The coordinate span of a predicate.** The subspace of `EuclideanSpace ℂ n` spanned by the
standard basis vectors at indices satisfying the decidable predicate `P`; equivalently, the
subspace of vectors supported on `P`. -/
noncomputable def coordinateSpan (P : n → Prop) [DecidablePred P] :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range fun i : {i // P i} => EuclideanSpace.basisFun n ℂ i.val)

/-- **Coordinate restriction.** Restrict a vector of `EuclideanSpace ℂ n` to the coordinates
satisfying `P`, landing in `EuclideanSpace ℂ {i // P i}`. -/
noncomputable def coordinateRestrict (P : n → Prop) [DecidablePred P]
    (φ : EuclideanSpace ℂ n) : EuclideanSpace ℂ {i // P i} :=
  WithLp.toLp 2 (fun i : {i // P i} => (WithLp.ofLp φ) i.val)

/-- **Generic block-transport of the unique-ground-state predicate.** If `H` is supported on the
coordinate block of a decidable predicate `P` (`H = P̂ · H · P̂`, with `P̂` the diagonal indicator of
`P`), then `H` having a fixed candidate `φ` as its unique ground state on the coordinate span of `P`
is equivalent to the submatrix restriction of `H` to that block having the restricted candidate
`coordinateRestrict P φ` as its unique ground state on the whole restricted space `⊤`. -/
theorem isUniqueGroundStateOn_coordinateSpan_iff_submatrix {H : Matrix n n ℂ}
    {P : n → Prop} [DecidablePred P]
    (hblock : H = Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0) * H
        * Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0))
    {E : ℝ} {φ : EuclideanSpace ℂ n} :
    IsUniqueGroundStateOn (coordinateSpan P) H E φ ↔
      IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ {i // P i}))
        (H.submatrix Subtype.val Subtype.val) E (coordinateRestrict P φ) := by
  sorry

/-- **The kernel of a block-diagonal matrix is the coordinate span of its zero-block predicate.**
If a diagonal matrix's entries vanish exactly on a decidable predicate `P`, its kernel (as a
subspace of `EuclideanSpace ℂ n`) is the coordinate span of `P`. -/
theorem matrixKernel_diagonal_eq_coordinateSpan (d : n → ℂ) (P : n → Prop) [DecidablePred P]
    (hP : ∀ i, d i = 0 ↔ P i) :
    matrixKernel (Matrix.diagonal d) = coordinateSpan P := by
  sorry

end LatticeSystem.Math
