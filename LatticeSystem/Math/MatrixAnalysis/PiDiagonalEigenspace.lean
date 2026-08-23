import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The eigenspace of a diagonal matrix on the Pi carrier (Theorem 10.4 arc, PR-15b)

Generic layer item for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc (issue
#5320, PR-15b). At `N = 0` the repulsive Hubbard Hamiltonian on the plain function carrier (Pi
type, `n → ℂ`, `Matrix.mulVecLin`) is a `Matrix.diagonal`, and its ground submodule is identified
with a single diagonal eigenspace. This file supplies the two model-independent facts needed for
that identification: a support characterization of membership in the eigenspace, and its
`finrank`.

## Main results

* `mem_eigenspace_diagonal_mulVecLin_iff` — `v` lies in the `L`-eigenspace of
  `(Matrix.diagonal d).mulVecLin` iff every coordinate `i` with `d i ≠ L` vanishes on `v`.
* `finrank_eigenspace_diagonal_mulVecLin` — that eigenspace has `finrank` equal to the number of
  coordinates `i` with `d i = L`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Math

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Support characterization of a diagonal matrix's eigenspace.** A vector `v : n → ℂ` lies in
the `L`-eigenspace of `(Matrix.diagonal d).mulVecLin` iff it vanishes at every coordinate `i` where
`d i ≠ L`. -/
theorem mem_eigenspace_diagonal_mulVecLin_iff (d : n → ℂ) (L : ℂ) (v : n → ℂ) :
    v ∈ Module.End.eigenspace (Matrix.diagonal d).mulVecLin L ↔
      ∀ i, d i ≠ L → v i = 0 := by
  sorry

/-- **`finrank` of a diagonal matrix's eigenspace.** The `L`-eigenspace of
`(Matrix.diagonal d).mulVecLin` has dimension equal to the number of coordinates `i` with
`d i = L` (`Nat.card`, avoiding a spurious `DecidablePred` hypothesis on the statement). -/
theorem finrank_eigenspace_diagonal_mulVecLin (d : n → ℂ) (L : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.diagonal d).mulVecLin L)
      = Nat.card {i // d i = L} := by
  sorry

end LatticeSystem.Math
