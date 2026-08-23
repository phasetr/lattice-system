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
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, funext_iff]
  constructor
  · intro h i hi
    have hcoord : (d i - L) * v i = 0 := by
      have := h i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
      linear_combination this
    exact (mul_eq_zero.mp hcoord).resolve_left (sub_ne_zero.mpr hi)
  · intro h i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : d i = L
    · rw [hi]
    · rw [h i hi, mul_zero, mul_zero]

/-- **`finrank` of a diagonal matrix's eigenspace.** The `L`-eigenspace of
`(Matrix.diagonal d).mulVecLin` has dimension equal to the number of coordinates `i` with
`d i = L` (`Nat.card`, avoiding a spurious `DecidablePred` hypothesis on the statement). -/
theorem finrank_eigenspace_diagonal_mulVecLin (d : n → ℂ) (L : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.diagonal d).mulVecLin L)
      = Nat.card {i // d i = L} := by
  have hker : Module.End.eigenspace (Matrix.diagonal d).mulVecLin L
      = LinearMap.ker (Matrix.diagonal (fun i => d i - L)).mulVecLin := by
    ext v
    rw [mem_eigenspace_diagonal_mulVecLin_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      funext_iff]
    constructor
    · intro h i
      rw [Matrix.mulVec_diagonal, Pi.zero_apply]
      by_cases hi : d i = L
      · rw [hi, sub_self, zero_mul]
      · rw [h i hi, mul_zero]
    · intro h i hi
      have := h i
      rw [Matrix.mulVec_diagonal, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hi)
  have hrange : Module.finrank ℂ
      (LinearMap.range (Matrix.diagonal (fun i => d i - L)).mulVecLin)
      = Fintype.card {i // d i - L ≠ 0} := Matrix.rank_diagonal _
  have hcompl : Fintype.card {i // d i - L ≠ 0} = Fintype.card {i // ¬ d i = L} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => sub_ne_zero)
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.diagonal (fun i => d i - L)).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, hrange, hcompl,
    Fintype.card_subtype_compl (fun i => d i = L)] at hrn
  have hle : Fintype.card {i // d i = L} ≤ Fintype.card n := Fintype.card_subtype_le _
  rw [hker, Nat.card_eq_fintype_card]
  omega

end LatticeSystem.Math
