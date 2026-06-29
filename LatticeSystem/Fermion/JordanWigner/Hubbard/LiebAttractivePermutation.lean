import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionicTranslation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInterleave

/-!
# The signed permutation operator for the block ↔ interleaved relabeling (Tasaki §10.2.1)

Twelfth layer (PR12) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

To connect the block-order coefficient-matrix results to the actual interleaved
Hamiltonian, the Fock operators must be transported through the orbital permutation
of PR11. This file builds the second-quantized **signed permutation operator** for
an arbitrary orbital permutation (generalizing the cyclic `translationOperator` of
§11.4, reusing the already-general `translationJwSign`), specializes it to the
block ↔ interleaved permutation, and proves it is unitary. The conjugation of the
creation/annihilation operators is a later layer.

## Main definitions

* `permutationOperator` — the signed permutation operator `|σ⟩ ↦ ε(π,σ) |σ ∘ π⁻¹⟩`
  for an arbitrary `π : Equiv.Perm (Fin M)`.
* `hubbardBlockToSpinfulPermutationOperator` — its specialization to the block ↔
  interleaved orbital permutation.

## Main results

* `permutationOperator_mulVec_basisVec` / `permutationOperator_refl` — the basis
  action and the identity at `π = refl`.
* `hubbardBlockToSpinfulPermutationOperator_mulVec_basisVec` — the basis action,
  carrying a block config to its interleaved relabeling.
* `hubbardBlockToSpinfulPermutationOperator_conjTranspose_mul` /
  `…_mul_conjTranspose` — unitarity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The signed permutation operator for an arbitrary orbital permutation `π`,
acting on the occupation basis as `|σ⟩ ↦ ε(π,σ) |σ ∘ π⁻¹⟩`. -/
noncomputable def permutationOperator (π : Equiv.Perm (Fin M)) : ManyBodyOp (Fin M) :=
  Matrix.of fun τ σ => if τ = σ ∘ π.symm then translationJwSign π σ else 0

/-- The Jordan–Wigner sign is real (`±1`), so `star`-invariant. -/
theorem translationJwSign_star (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2) :
    star (translationJwSign π σ) = translationJwSign π σ := by
  unfold translationJwSign
  rw [star_pow]
  norm_num

/-- The defining action of the signed permutation operator on basis states. -/
theorem permutationOperator_mulVec_basisVec (π : Equiv.Perm (Fin M))
    (σ : Fin M → Fin 2) :
    (permutationOperator π).mulVec (basisVec σ)
      = translationJwSign π σ • basisVec (σ ∘ π.symm) := by
  funext τ
  have h : (permutationOperator π).mulVec (basisVec σ) τ = permutationOperator π τ σ :=
    sum_mul_basisVec σ (fun ρ => permutationOperator π τ ρ)
  rw [h, permutationOperator, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  split_ifs with hτ <;> simp

/-- The signed permutation operator at `π = refl` is the identity. -/
theorem permutationOperator_refl (M : ℕ) :
    permutationOperator (Equiv.refl (Fin M)) = 1 := by
  ext τ σ
  have hsign : translationJwSign (Equiv.refl (Fin M)) σ = 1 := by
    unfold translationJwSign
    rw [Finset.filter_false_of_mem, Finset.card_empty, pow_zero]
    rintro p _ ⟨hlt, -, -, hgt⟩
    exact absurd (hlt.trans hgt) (lt_irrefl _)
  rw [permutationOperator, Matrix.of_apply, Equiv.refl_symm]
  simp only [Equiv.coe_refl, Function.comp_id, Matrix.one_apply]
  split_ifs with h
  · exact hsign
  · rfl

/-- The signed permutation operator is unitary (`Uᴴ U = 1`). -/
theorem permutationOperator_conjTranspose_mul (π : Equiv.Perm (Fin M)) :
    (permutationOperator π)ᴴ * permutationOperator π = 1 := by
  have hinj : ∀ {a b : Fin M → Fin 2}, a ∘ π.symm = b ∘ π.symm → a = b := by
    intro a b h
    funext y
    have := congrFun h (π y)
    simpa [Equiv.symm_apply_apply] using this
  ext σ σ'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permutationOperator, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ ∘ π.symm)]
  · by_cases hσ : σ = σ'
    · subst hσ
      simp [translationJwSign_star, translationJwSign_sq]
    · rw [if_neg (fun h => hσ (hinj h)), mul_zero, if_neg hσ]
  · intro τ _ hτ
    rw [if_neg (fun h => hτ h), star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The signed permutation operator is unitary (`U Uᴴ = 1`). -/
theorem permutationOperator_mul_conjTranspose (π : Equiv.Perm (Fin M)) :
    permutationOperator π * (permutationOperator π)ᴴ = 1 :=
  mul_eq_one_comm.mp (permutationOperator_conjTranspose_mul π)

/-! ## The block ↔ interleaved permutation operator -/

/-- The signed permutation operator for the block ↔ interleaved orbital relabeling. -/
noncomputable def hubbardBlockToSpinfulPermutationOperator (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)

/-- The basis action of the block ↔ interleaved permutation operator. -/
theorem hubbardBlockToSpinfulPermutationOperator_mulVec_basisVec (N : ℕ)
    (c : Fin (2 * N + 2) → Fin 2) :
    (hubbardBlockToSpinfulPermutationOperator N).mulVec (basisVec c)
      = translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N) c •
          basisVec (hubbardBlockToSpinfulConfigEquiv N c) := by
  rw [hubbardBlockToSpinfulPermutationOperator, permutationOperator_mulVec_basisVec]
  rfl

/-- The block ↔ interleaved permutation operator is unitary (`Uᴴ U = 1`). -/
theorem hubbardBlockToSpinfulPermutationOperator_conjTranspose_mul (N : ℕ) :
    (hubbardBlockToSpinfulPermutationOperator N).conjTranspose *
      hubbardBlockToSpinfulPermutationOperator N = 1 :=
  permutationOperator_conjTranspose_mul (hubbardBlockToSpinfulOrbitalEquiv N)

/-- The block ↔ interleaved permutation operator is unitary (`U Uᴴ = 1`). -/
theorem hubbardBlockToSpinfulPermutationOperator_mul_conjTranspose (N : ℕ) :
    hubbardBlockToSpinfulPermutationOperator N *
      (hubbardBlockToSpinfulPermutationOperator N).conjTranspose = 1 :=
  permutationOperator_mul_conjTranspose (hubbardBlockToSpinfulOrbitalEquiv N)

end LatticeSystem.Fermion
