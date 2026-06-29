import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePermConj

/-!
# The block up-kinetic operator and its fixed matrix are Hermitian (Tasaki §10.2.1)

Twenty-first layer (PR21) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

For a Hermitian hopping matrix `T` (`star (T i j) = T j i`, in particular any real
symmetric `T`), the block-order up-kinetic operator `hubbardBlockKineticUp` is
Hermitian (the same argument as `fermionHopping_isHermitian`, with the mode
indices replaced by the block indices `hubbardBlockIndex N i 0`). Consequently its
gauge-fixed left-multiplier matrix `A = hubbardBlockKineticUpFixedMatrix` is
Hermitian (`Aᴴ = A`): its entries are operator matrix elements between block-merge
configurations, and the Hermitian operator's entries are conjugate-symmetric.

This is the Hermitian half of the reflection-positive Gram input. Combined with the
entrywise reality (`Aᵀ = A`, a later layer), it yields `Aᴴ = Aᵀ` and hence
`Bᵣ = P·Aᴴ·P`, which the SRP energy bound consumes via
`spinReflection_gramMatrix_nonneg`.

## Main results

* `hubbardBlockKineticUp_isHermitian` — the block up-kinetic operator is Hermitian
  for Hermitian `T`.
* `hubbardBlockKineticUpFixedMatrix_isHermitian` — its fixed left-multiplier matrix
  `A` is Hermitian (`Aᴴ = A`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The block-order up-kinetic operator `Σ_{i,j} T_{i,j} ĉ†_{i,↑} ĉ_{j,↑}` is
Hermitian when the hopping matrix `T` is Hermitian (`star (T i j) = T j i`). The
conjugate transpose flips creation/annihilation and reverses the index order; an
`i ↔ j` reindexing brings the sum back to its original form. -/
theorem hubbardBlockKineticUp_isHermitian (N : ℕ)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : ∀ i j, star (T i j) = T j i) :
    (hubbardBlockKineticUp N T).IsHermitian := by
  change (hubbardBlockKineticUp N T)ᴴ = hubbardBlockKineticUp N T
  unfold hubbardBlockKineticUp
  calc (∑ i, ∑ j, T i j • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
          fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)))ᴴ
      = ∑ i, ∑ j, T j i • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N j 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N i 0)) := by
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
          fermionHoppingTerm_conjTranspose, hT]
    _ = ∑ j, ∑ i, T j i • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N j 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N i 0)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, T i j • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)) := rfl

/-- The gauge-fixed up-kinetic left-multiplier matrix `A` is Hermitian (`Aᴴ = A`)
for Hermitian `T`: its entries are matrix elements of the Hermitian operator
`hubbardBlockKineticUp` between block-merge configurations. -/
theorem hubbardBlockKineticUpFixedMatrix_isHermitian (N : ℕ)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : ∀ i j, star (T i j) = T j i) :
    (hubbardBlockKineticUpFixedMatrix N T).IsHermitian := by
  have hop := hubbardBlockKineticUp_isHermitian N hT
  change (hubbardBlockKineticUpFixedMatrix N T)ᴴ = hubbardBlockKineticUpFixedMatrix N T
  funext u u'
  rw [Matrix.conjTranspose_apply]
  simp only [hubbardBlockKineticUpFixedMatrix, hubbardBlockKineticUpCoeffMatrix]
  have h := congrFun (congrFun hop
    (hubbardBlockMergeConfig N u (particleHoleConfig N (fun _ => 0))))
    (hubbardBlockMergeConfig N u' (particleHoleConfig N (fun _ => 0)))
  rwa [Matrix.conjTranspose_apply] at h

end LatticeSystem.Fermion
