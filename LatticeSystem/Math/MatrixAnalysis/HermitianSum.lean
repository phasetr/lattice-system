import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Closure of Hermitian-ness under finite sums and commuting products

Small generic linear-algebra facts extracted from several physics files where they had been
re-proved as private helpers:

* `Matrix.isHermitian_sum` — a finite sum of Hermitian matrices is Hermitian (extracted from
  `Quantum/IsingChain.lean`, `Quantum/TotalSpin.lean`, `Quantum/SpinS/*`).
* `Matrix.IsHermitian.mul_of_commute` — the product of two commuting Hermitian matrices is
  Hermitian (previously sitting in the widely-imported physics file `Quantum/ManyBody.lean`).

mathlib has `Matrix.conjTranspose_sum`, `Matrix.conjTranspose_mul`, and `Matrix.isHermitian_zero`,
but no packaged `Finset.sum` version nor the commuting-product corollary.
-/

namespace Matrix

variable {ι : Type*} {n : Type*}

/-- A finite sum of Hermitian matrices is Hermitian. -/
theorem isHermitian_sum (s : Finset ι) {f : ι → Matrix n n ℂ}
    (hf : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  classical
  refine Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) Matrix.isHermitian_zero ?_
  exact hf

/-- The product of two commuting Hermitian matrices is Hermitian. -/
theorem IsHermitian.mul_of_commute [Fintype n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hcomm : A * B = B * A) : (A * B).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hA, hB, hcomm]

end Matrix
