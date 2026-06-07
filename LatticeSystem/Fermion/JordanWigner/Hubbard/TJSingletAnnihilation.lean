import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Tasaki 11.5.3: the singlet annihilation operator (Theorem 11.26 PR3c-prep)

The two-site Heisenberg bond `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y` equals `½ Δ_xy† Δ_xy` for the **singlet
annihilation** operator `Δ_xy = ĉ_{y↓} ĉ_{x↑} − ĉ_{y↑} ĉ_{x↓}` (a global operator identity; see the
follow-up).  This file sets up `Δ_xy`:

* `tJSingletAnnihilation x y` — `ĉ_{y↓} ĉ_{x↑} − ĉ_{y↑} ĉ_{x↓}`;
* `tJSingletAnnihilation_conjTranspose` — `Δ_xy† = ĉ†_{x↑} ĉ†_{y↓} − ĉ†_{x↓} ĉ†_{y↑}`;
* `tJSingletAnnihilation_mulVec_allUpState` — `Δ_xy |↑…↑⟩ = 0` (the singlet annihilator kills the
  fully aligned maximal-spin state), so the all-up state has bond energy `0`.

The positive-semidefiniteness `Δ_xy† Δ_xy ≥ 0` will give the ferromagnetic Heisenberg ground energy.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The singlet annihilation operator** `Δ_xy = ĉ_{y↓} ĉ_{x↑} − ĉ_{y↑} ĉ_{x↓}` on the edge
`(x, y)`.  It annihilates the bond singlet pair; `Δ_xy† Δ_xy` is the (positive-semidefinite)
Heisenberg bond `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y` up to a factor `½`. -/
noncomputable def tJSingletAnnihilation (N : ℕ) (x y : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionDownAnnihilation N y * fermionUpAnnihilation N x -
    fermionUpAnnihilation N y * fermionDownAnnihilation N x

/-- `Δ_xy† = ĉ†_{x↑} ĉ†_{y↓} − ĉ†_{x↓} ĉ†_{y↑}`. -/
theorem tJSingletAnnihilation_conjTranspose (N : ℕ) (x y : Fin (N + 1)) :
    (tJSingletAnnihilation N x y)ᴴ =
      fermionUpCreation N x * fermionDownCreation N y -
        fermionDownCreation N x * fermionUpCreation N y := by
  unfold tJSingletAnnihilation fermionDownAnnihilation fermionUpAnnihilation
    fermionUpCreation fermionDownCreation
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiAnnihilation_conjTranspose,
    fermionMultiAnnihilation_conjTranspose, fermionMultiAnnihilation_conjTranspose]

/-- **The singlet annihilator kills the all-up state.**  `Δ_xy |↑…↑⟩ = 0`: both `ĉ_{x↓}` and
`ĉ_{y↓}` annihilate the down-free `|↑…↑⟩` (the latter after anticommuting `ĉ_{y↓}` past the
different-orbital `ĉ_{x↑}`).  Hence `|↑…↑⟩` has zero Heisenberg bond energy. -/
theorem tJSingletAnnihilation_mulVec_allUpState (N : ℕ) (x y : Fin (N + 1)) :
    (tJSingletAnnihilation N x y).mulVec (hubbardAllUpState N) = 0 := by
  rw [tJSingletAnnihilation, Matrix.sub_mulVec]
  have hterm2 : (fermionUpAnnihilation N y * fermionDownAnnihilation N x).mulVec
      (hubbardAllUpState N) = 0 := by
    rw [← Matrix.mulVec_mulVec, fermionDownAnnihilation_mulVec_allUpState, Matrix.mulVec_zero]
  have hanti : fermionDownAnnihilation N y * fermionUpAnnihilation N x =
      -(fermionUpAnnihilation N x * fermionDownAnnihilation N y) := by
    unfold fermionDownAnnihilation fermionUpAnnihilation
    have h := fermionMultiAnnihilation_anticomm_of_ne (N := 2 * N + 1)
      (i := spinfulIndex N y 1) (j := spinfulIndex N x 0) (spinfulIndex_up_ne_down N x y).symm
    linear_combination (norm := noncomm_ring) h
  have hterm1 : (fermionDownAnnihilation N y * fermionUpAnnihilation N x).mulVec
      (hubbardAllUpState N) = 0 := by
    rw [hanti, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      fermionDownAnnihilation_mulVec_allUpState, Matrix.mulVec_zero, neg_zero]
  rw [hterm1, hterm2, sub_zero]

end LatticeSystem.Fermion
