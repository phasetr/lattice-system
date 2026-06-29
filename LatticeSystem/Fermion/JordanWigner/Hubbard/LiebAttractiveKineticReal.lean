import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticHermitian

/-!
# The fixed up-kinetic matrix is real, giving `Bᵣ = Pmat·Aᴴ·Pmat` (Tasaki §10.2.1)

Twenty-second layer (PR22) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

The reflection-positivity Gram bound `0 ≤ Re tr(C·A·C·Aᴴ)`
(`spinReflection_gramMatrix_nonneg`) consumes the *adjoint* `Aᴴ`, while PR20 gives
the right-multiplier `Bᵣ` as a *transpose* conjugation `Bᵣ = Pmat·Aᵀ·Pmat`. For a
Hermitian operator these differ (e.g. for `σ_y`, `tr(A·Aᵀ) < 0`), so the bridge
genuinely needs the entrywise **reality** of `A`.

For a real hopping matrix `T` (`star (T i j) = T i j`) the fixed up-kinetic matrix
`A = hubbardBlockKineticUpFixedMatrix` has real entries: each entry is a sum of
`T_{ij}` times a hopping matrix element, which is a product of Jordan–Wigner string
signs `±1` (real). Hence `Aᴴ = Aᵀ`, upgrading PR20 to

  `Bᵣ = Pmat·Aᴴ·Pmat`,

the adjoint form the SRP energy bound consumes.

## Main results

* `jwSign_star` — the Jordan–Wigner string sign is real.
* `fermionHoppingTerm_entry_real` — a hopping matrix element is real.
* `hubbardBlockKineticUpFixedMatrix_conjTranspose_eq_transpose` — `Aᴴ = Aᵀ` for
  real `T`.
* `hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose` —
  `Bᵣ = Pmat·Aᴴ·Pmat` for real `T`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A complex matrix with real entries has equal adjoint and transpose. -/
theorem conjTranspose_eq_transpose_of_entry_real {ι κ : Type*} {A : Matrix ι κ ℂ}
    (hA : ∀ i j, star (A i j) = A i j) : Aᴴ = Aᵀ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, hA]

/-- The Jordan–Wigner string sign is real (a product of `±1`). -/
theorem jwSign_star (M : ℕ) (j : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) :
    star (jwSign M j c) = jwSign M j c := by
  unfold jwSign
  rw [star_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

/-- A single hopping matrix element `(ĉ†_p ĉ_q)_{a,b}` is real: it is either `0`
or a product of two Jordan–Wigner string signs. -/
theorem fermionHoppingTerm_entry_real (M : ℕ) (p q : Fin (M + 1))
    (a b : Fin (M + 1) → Fin 2) :
    star ((fermionMultiCreation M p * fermionMultiAnnihilation M q) a b)
      = (fermionMultiCreation M p * fermionMultiAnnihilation M q) a b := by
  have hentry : (fermionMultiCreation M p * fermionMultiAnnihilation M q) a b
      = ((fermionMultiCreation M p * fermionMultiAnnihilation M q).mulVec (basisVec b)) a := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_mul_basisVec b _]
  rw [hentry, fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split_ifs with h
  · rw [Pi.smul_apply, smul_eq_mul, star_mul', star_mul', jwSign_star, jwSign_star,
      basisVec_apply]
    split_ifs <;> simp
  · simp

/-- The fixed up-kinetic matrix `A` has real entries for a real hopping matrix `T`. -/
theorem hubbardBlockKineticUpFixedMatrix_entry_real (N : ℕ)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : ∀ i j, star (T i j) = T i j)
    (u u' : hubbardSpinConfig N) :
    star (hubbardBlockKineticUpFixedMatrix N T u u')
      = hubbardBlockKineticUpFixedMatrix N T u u' := by
  simp only [hubbardBlockKineticUpFixedMatrix, hubbardBlockKineticUpCoeffMatrix,
    hubbardBlockKineticUp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [star_mul', hT, fermionHoppingTerm_entry_real]

/-- **`Aᴴ = Aᵀ`**: the fixed up-kinetic matrix has equal adjoint and transpose for
a real hopping matrix `T`. -/
theorem hubbardBlockKineticUpFixedMatrix_conjTranspose_eq_transpose (N : ℕ)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : ∀ i j, star (T i j) = T i j) :
    (hubbardBlockKineticUpFixedMatrix N T)ᴴ = (hubbardBlockKineticUpFixedMatrix N T)ᵀ :=
  conjTranspose_eq_transpose_of_entry_real
    (hubbardBlockKineticUpFixedMatrix_entry_real N hT)

/-- **The down/up kinetic adjoint relation `Bᵣ = Pmat·Aᴴ·Pmat`** for a real hopping
matrix `T`. Upgrades PR20's transpose form to the adjoint form consumed by the
spin-reflection Gram bound. -/
theorem hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose (N : ℕ)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : ∀ i j, star (T i j) = T i j) :
    hubbardBlockKineticDownFixedRightMatrix N T
      = particleHoleConfigPermMatrix N * (hubbardBlockKineticUpFixedMatrix N T)ᴴ
          * particleHoleConfigPermMatrix N := by
  rw [hubbardBlockKineticDownFixedRightMatrix_eq_permConj,
    hubbardBlockKineticUpFixedMatrix_conjTranspose_eq_transpose N hT]

end LatticeSystem.Fermion
