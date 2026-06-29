import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePermConj
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionTrace

/-!
# Particle-hole conjugation facts for the reconciliation `W := C·P` (Tasaki §10.2.4)

Thirty-third layer (PR33c) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

The energy reconciliation expresses the half-filled energy as the abstract
`liebSRPEnergy` on `W := C·P`, where `P := particleHoleConfigPermMatrix` is the
permutation matrix of the particle-hole involution on configurations. This file
collects the elementary facts about `P` and its conjugation action needed to
assemble that identity:

* `P` is a **Hermitian involution** (`P·P = 1`, `Pᴴ = P`).
* conjugating a diagonal by `P` reindexes it by the involution
  (`P·diagonal d·P = diagonal (d ∘ φ)`);
* the hole-occupation diagonal is the particle-hole conjugate of the
  up-occupation diagonal: `E_x = P·D_x·P`.

The last fact is exactly the `I_x = P·D_x·P` input that turns the interaction trace
`tr(Cᴴ·D_x·C·E_x)` into the clean `liebSRPEnergy` form `tr(W·D_x·W·D_x)` (PR33b).

## Main results

* `particleHoleConfigPermMatrix_mul_self` — `P·P = 1`.
* `particleHoleConfigPermMatrix_isHermitian` — `Pᴴ = P`.
* `particleHoleConfigPermMatrix_conj_diagonal` — `P·diagonal d·P = diagonal (d ∘ φ)`.
* `hubbardUpOccupationDiag_isHermitian` — `D_x` is Hermitian.
* `hubbardHoleOccupationDiag_eq_permConj` — `E_x = P·D_x·P`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix PEquiv
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- Entrywise formula for the particle-hole permutation matrix:
`P i j = if φ i = j then 1 else 0` where `φ = particleHoleConfigEquiv`. -/
theorem particleHoleConfigPermMatrix_apply (i j : hubbardSpinConfig N) :
    particleHoleConfigPermMatrix N i j
      = if particleHoleConfigEquiv N i = j then 1 else 0 := by
  simp only [particleHoleConfigPermMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, eq_comm]

/-- The involution identity `φ (φ i) = i` for the particle-hole equivalence. -/
private theorem particleHoleConfigEquiv_apply_apply (i : hubbardSpinConfig N) :
    particleHoleConfigEquiv N (particleHoleConfigEquiv N i) = i := by
  simp only [particleHoleConfigEquiv, Function.Involutive.coe_toPerm]
  exact particleHoleConfig_involutive N i

/-- The particle-hole permutation matrix is an involution: `P·P = 1`. -/
theorem particleHoleConfigPermMatrix_mul_self :
    particleHoleConfigPermMatrix N * particleHoleConfigPermMatrix N = 1 := by
  funext i j
  rw [Matrix.mul_apply]
  simp only [particleHoleConfigPermMatrix_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [particleHoleConfigEquiv_apply_apply, Matrix.one_apply]

/-- The particle-hole permutation matrix is Hermitian: `Pᴴ = P`. -/
theorem particleHoleConfigPermMatrix_isHermitian :
    (particleHoleConfigPermMatrix N).IsHermitian := by
  funext i j
  rw [Matrix.conjTranspose_apply, particleHoleConfigPermMatrix_apply,
    particleHoleConfigPermMatrix_apply]
  have hflip : particleHoleConfigEquiv N j = i ↔ particleHoleConfigEquiv N i = j := by
    constructor <;> intro h
    · rw [← h, particleHoleConfigEquiv_apply_apply]
    · rw [← h, particleHoleConfigEquiv_apply_apply]
  by_cases h : particleHoleConfigEquiv N i = j
  · rw [if_pos h, if_pos (hflip.mpr h), star_one]
  · rw [if_neg h, if_neg (fun h' => h (hflip.mp h')), star_zero]

/-- **Conjugating a diagonal matrix by the particle-hole permutation** reindexes
it by the involution: `P·diagonal d·P = diagonal (fun k => d (φ k))`. -/
theorem particleHoleConfigPermMatrix_conj_diagonal (d : hubbardSpinConfig N → ℂ) :
    particleHoleConfigPermMatrix N * Matrix.diagonal d * particleHoleConfigPermMatrix N
      = Matrix.diagonal (fun k => d (particleHoleConfigEquiv N k)) := by
  simp only [particleHoleConfigPermMatrix, toMatrix_toPEquiv_mul, mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix]
  funext i j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Function.comp_apply, id_eq,
    particleHoleConfigEquiv_symm, (particleHoleConfigEquiv N).injective.eq_iff]

/-- A single-orbital occupation flip negates the occupation value over `ℂ`:
`((flipOccupation a).val : ℂ) = 1 - (a.val : ℂ)` for `a : Fin 2`. -/
theorem flipOccupation_val_complex (a : Fin 2) :
    ((flipOccupation a).val : ℂ) = 1 - (a.val : ℂ) := by
  fin_cases a <;> simp [flipOccupation]

/-- The up-occupation diagonal is Hermitian (real diagonal entries). -/
theorem hubbardUpOccupationDiag_isHermitian (x : Fin (N + 1)) :
    (hubbardUpOccupationDiag N x).IsHermitian :=
  (hubbardUpOccupationDiag_posSemidef N x).isHermitian

/-- **The hole-occupation diagonal is the particle-hole conjugate of the
up-occupation diagonal:** `E_x = P·D_x·P`. -/
theorem hubbardHoleOccupationDiag_eq_permConj (x : Fin (N + 1)) :
    hubbardHoleOccupationDiag N x
      = particleHoleConfigPermMatrix N * hubbardUpOccupationDiag N x
          * particleHoleConfigPermMatrix N := by
  simp only [hubbardUpOccupationDiag, hubbardHoleOccupationDiag]
  rw [particleHoleConfigPermMatrix_conj_diagonal]
  congr 1
  funext h
  simp only [particleHoleConfigEquiv, Function.Involutive.coe_toPerm, particleHoleConfig,
    flipOccupation_val_complex]

end LatticeSystem.Fermion
