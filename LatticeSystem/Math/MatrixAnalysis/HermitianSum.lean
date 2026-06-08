import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Finite sums of Hermitian matrices are Hermitian

A small generic linear-algebra fact, `Matrix.isHermitian_sum`, extracted from several physics files
(`Quantum/IsingChain.lean`, `Quantum/TotalSpin.lean`, `Quantum/SpinS/*`) where it had been re-proved
as a private helper.  mathlib has `Matrix.conjTranspose_sum` and `Matrix.isHermitian_zero` but no
packaged `Finset.sum` version.
-/

namespace Matrix

variable {ι : Type*} {n : Type*}

/-- A finite sum of Hermitian matrices is Hermitian. -/
theorem isHermitian_sum (s : Finset ι) {f : ι → Matrix n n ℂ}
    (hf : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  classical
  refine Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) Matrix.isHermitian_zero ?_
  exact hf

end Matrix
