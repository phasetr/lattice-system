import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBrRelation
import Mathlib.Data.Matrix.PEquiv

/-!
# The down/up kinetic adjoint relation as a permutation conjugation (Tasaki §10.2.1)

Twentieth layer (PR20) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR18 proved the entrywise adjoint relation `Bᵣ h h' = A (P h') (P h)` between the
right multiplier `Bᵣ = hubbardBlockKineticDownFixedRightMatrix` and the left
multiplier `A = hubbardBlockKineticUpFixedMatrix`, with `P = particleHoleConfig`.
This file repackages it as an honest **matrix** identity

  `Bᵣ = Pmat · Aᵀ · Pmat`,

where `Pmat = particleHoleConfigPermMatrix` is the permutation matrix of the
particle–hole involution. Having the relation as matrix algebra (rather than
entrywise) keeps the subsequent reflection-positive trace manipulations
(`tr(Cᴴ·(A·C + C·Bᵣ))` → the SRP Gram form) free of entrywise rewriting.

## Main definitions

* `particleHoleConfigPermMatrix` — the permutation matrix of the particle–hole
  involution `particleHoleConfigEquiv` (which is its own inverse).

## Main results

* `particleHoleConfigEquiv_symm` — the particle–hole permutation is an involution.
* `hubbardBlockKineticDownFixedRightMatrix_eq_permConj` — `Bᵣ = Pmat · Aᵀ · Pmat`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum PEquiv
open scoped BigOperators

variable {N : ℕ}

/-- The permutation matrix of the particle–hole involution on configurations. -/
noncomputable def particleHoleConfigPermMatrix (N : ℕ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  (particleHoleConfigEquiv N).toPEquiv.toMatrix

/-- The particle–hole permutation is its own inverse (it is an involution). -/
theorem particleHoleConfigEquiv_symm (N : ℕ) :
    (particleHoleConfigEquiv N).symm = particleHoleConfigEquiv N :=
  Equiv.ext fun _ => rfl

/-- **The down/up kinetic adjoint relation as a permutation conjugation.** The
right multiplier matrix of the down kinetic action is the particle-hole
conjugation of the transposed up multiplier: `Bᵣ = Pmat · Aᵀ · Pmat`. -/
theorem hubbardBlockKineticDownFixedRightMatrix_eq_permConj (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) :
    hubbardBlockKineticDownFixedRightMatrix N T
      = particleHoleConfigPermMatrix N * (hubbardBlockKineticUpFixedMatrix N T)ᵀ
          * particleHoleConfigPermMatrix N := by
  funext h h'
  rw [hubbardBlockKineticDownFixedRightMatrix_eq_up]
  simp only [particleHoleConfigPermMatrix, mul_toMatrix_toPEquiv, toMatrix_toPEquiv_mul,
    Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]
  rw [particleHoleConfigEquiv_symm]
  simp only [particleHoleConfigEquiv, Function.Involutive.coe_toPerm]

end LatticeSystem.Fermion
