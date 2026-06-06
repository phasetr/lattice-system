import LatticeSystem.Fermion.JordanWigner.Hubbard.TJEffMatrix

/-!
# Tasaki 11.5: the real-symmetric t-J sector effective matrix (Prop 11.24 PR-B8)

The Perron–Frobenius step of Proposition 11.24 acts on the t-J effective matrix *restricted to the
fixed `N̂ = Ne`, `Ŝ³ = ½` sector* — exactly where the wrap-hop is sign-free (odd `Ne`) and the
entries are real.  This file sets up that restriction, mirroring the Nagaoka template
(`tasakiEffReMatrix` / `tasakiEffReMatrixOnSector` / `nagaokaPFMatrixOnSector_isSymm`):

* `TJSpinHalfFillingSector N Ne` — the sector states `s : Fin (N+1) → Fin 3` with
  `#↑ = #↓ + 1` (so `Ŝ³ = ½`) and `#↑ + #↓ = Ne` (so `N̂ = Ne`);
* `tJEffReMatrix` — the real part of the (Hermitian) complex effective matrix `tJEffMatrix`;
* `tJEffReMatrixOnSector` — its restriction to the sector via `submatrix Subtype.val`;
* `tJEffReMatrixOnSector_isSymm` — symmetry, from the Hermiticity of `tJEffMatrix` (the real parts
  of `M_{q,p}` and `M_{p,q} = conj M_{q,p}` agree); no global realness of the full matrix is needed.

This is the `Matrix … ℝ` that, once `−M` is shown irreducible on a non-empty sector, feeds Tasaki
Theorem A.18 (`perronFrobenius_real_symmetric`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum SimpleGraph

variable {N : ℕ}

/-- **The `N̂ = Ne`, `Ŝ³ = ½` sector of t-J site-states.**  The site-states `s : Fin (N+1) → Fin 3`
(`0/1/2 = ∅/↑/↓`) with one more `↑` than `↓` (`Ŝ³ = ½`) and total electron count `Ne`. -/
abbrev TJSpinHalfFillingSector (N Ne : ℕ) :=
  {s : Fin (N + 1) → Fin 3 //
    (Finset.univ.filter (fun k => s k = 1)).card
        = (Finset.univ.filter (fun k => s k = 2)).card + 1 ∧
      (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne}

/-- **The real t-J effective matrix.**  The real part of the (Hermitian) complex effective matrix
`tJEffMatrix`.  Within the `N̂ = Ne`, `Ŝ³ = ½` sector its off-diagonal entries are non-positive
(`tJEffMatrix_offdiag_nonpos`) and it agrees with `tJEffMatrix`, so `tJEffMatrix` is a real matrix
in disguise there. -/
noncomputable def tJEffReMatrix (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) : Matrix (Fin (N + 1) → Fin 3) (Fin (N + 1) → Fin 3) ℝ :=
  fun s' s => (tJEffMatrix N G τ J s' s).re

/-- **The real t-J effective matrix restricted to the `N̂ = Ne`, `Ŝ³ = ½` sector.**  The real
symmetric matrix to which Perron–Frobenius is applied in the proof of Proposition 11.24. -/
noncomputable def tJEffReMatrixOnSector (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    Matrix (TJSpinHalfFillingSector N Ne) (TJSpinHalfFillingSector N Ne) ℝ :=
  (tJEffReMatrix N G τ J).submatrix Subtype.val Subtype.val

/-- **The sector restriction of the real effective matrix is symmetric.**  Symmetry comes from the
Hermiticity of `tJEffMatrix` (`tJEffMatrix_isHermitian`): `M_{q,p} = conj M_{p,q}`, so their real
parts agree.  No global realness of the full matrix is required. -/
theorem tJEffReMatrixOnSector_isSymm (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    (tJEffReMatrixOnSector N Ne G τ J).IsSymm := by
  unfold tJEffReMatrixOnSector tJEffReMatrix
  ext p q
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  have h := congr_fun₂ (tJEffMatrix_isHermitian N G τ J) q.val p.val
  rw [Matrix.conjTranspose_apply] at h
  rw [← h, Complex.star_def, Complex.conj_re]

end LatticeSystem.Fermion
