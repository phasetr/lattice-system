import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaTransform
import Mathlib.Data.Matrix.PEquiv

/-!
# The Shiba permutation matrix and its conjugation facts (Tasaki §9.3.3)

Third layer (c3, permutation part) of the axiom-free portion of **Tasaki
Theorem 10.4** (Lieb's theorem for the repulsive Hubbard model at half-filling),
Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §9.3.3, pp. 334–337.

The Shiba transformation (eq. (9.3.48)) is realised, at the level of the Fock
occupation basis `Fin (2|Λ|) → Fin 2`, as a **signed permutation matrix**
`Û = diagonal (shibaSignFn) * shibaPermMatrix` (eq. (9.3.50)).  This file
supplies the **unsigned permutation part** `shibaPermMatrix`, the permutation
matrix of the involution `shibaConfigEquiv` (down-spin particle-hole flip,
eq. (9.3.48)), together with the elementary conjugation facts needed to build
and analyse `Û`:

* `Û`-independent facts: `shibaPermMatrix` is **Hermitian** (`Pᴴ = P`) and
  conjugating a diagonal by it reindexes the diagonal by the Shiba involution
  (`P·diagonal d·P = diagonal (d ∘ shibaConfig)`).

These are the exact Fock-space analogues of the attractive-side facts
`particleHoleConfigPermMatrix_isHermitian` / `_conj_diagonal`
(`LiebAttractivePHConjDiag.lean`), but on the full `2|Λ|`-mode configuration
space rather than the single-species one.

## Main definitions

* `shibaPermMatrix` — the permutation matrix of the Shiba involution
  `shibaConfigEquiv` on Fock configurations.

## Main results

* `shibaPermMatrix_apply` — entrywise formula.
* `shibaPermMatrix_mul_self` — `P·P = 1`.
* `shibaPermMatrix_isHermitian` — `Pᴴ = P`.
* `shibaPermMatrix_conj_diagonal` — `P·diagonal d·P = diagonal (d ∘ shibaConfig)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §9.3.3, eqs. (9.3.48)/(9.3.50), pp. 335–336;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum PEquiv
open scoped BigOperators

variable {N : ℕ}

/-- The **Shiba permutation matrix**: the permutation matrix of the Shiba
involution `shibaConfigEquiv` (the down-spin particle-hole flip, Tasaki
eq. (9.3.48)) on the Fock occupation configurations `Fin (2N+2) → Fin 2`.  It is
the unsigned part of the full Shiba unitary `Û` (eq. (9.3.50)). -/
noncomputable def shibaPermMatrix (N : ℕ) :
    Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
  (shibaConfigEquiv N).toPEquiv.toMatrix

/-- Entrywise formula for the Shiba permutation matrix:
`P i j = if shibaConfig i = j then 1 else 0`. -/
theorem shibaPermMatrix_apply (i j : Fin (2 * N + 2) → Fin 2) :
    shibaPermMatrix N i j = if shibaConfig N i = j then 1 else 0 := by
  simp only [shibaPermMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, eq_comm, shibaConfigEquiv_apply]

/-- The Shiba permutation matrix is an involution: `P·P = 1`.  Since `P` is the
permutation matrix of the involution `shibaConfig`, squaring it reindexes by
`shibaConfig ∘ shibaConfig = id`. -/
theorem shibaPermMatrix_mul_self :
    shibaPermMatrix N * shibaPermMatrix N = 1 := by
  funext i j
  rw [Matrix.mul_apply]
  simp only [shibaPermMatrix_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [shibaConfig_shibaConfig, Matrix.one_apply]

/-- The Shiba permutation matrix is Hermitian: `Pᴴ = P`. -/
theorem shibaPermMatrix_isHermitian :
    (shibaPermMatrix N).IsHermitian := by
  funext i j
  rw [Matrix.conjTranspose_apply, shibaPermMatrix_apply, shibaPermMatrix_apply]
  have hflip : shibaConfig N j = i ↔ shibaConfig N i = j := by
    constructor <;> intro h
    · rw [← h, shibaConfig_shibaConfig]
    · rw [← h, shibaConfig_shibaConfig]
  by_cases h : shibaConfig N i = j
  · rw [if_pos h, if_pos (hflip.mpr h), star_one]
  · rw [if_neg h, if_neg (fun h' => h (hflip.mp h')), star_zero]

/-- **Conjugating a diagonal matrix by the Shiba permutation** reindexes it by
the involution: `P·diagonal d·P = diagonal (fun k => d (shibaConfig k))`. -/
theorem shibaPermMatrix_conj_diagonal (d : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    shibaPermMatrix N * Matrix.diagonal d * shibaPermMatrix N
      = Matrix.diagonal (fun k => d (shibaConfig N k)) := by
  simp only [shibaPermMatrix, toMatrix_toPEquiv_mul, mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix]
  funext i j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Function.comp_apply, id_eq,
    shibaConfigEquiv_symm, shibaConfigEquiv_apply]
  by_cases h : i = j
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hc => h (by
      have := congrArg (shibaConfig N) hc
      rwa [shibaConfig_shibaConfig, shibaConfig_shibaConfig] at this))]

end LatticeSystem.Fermion
