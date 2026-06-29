import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePermutation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeff
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveReflection

/-!
# The SRP ↔ block coefficient bridge (Tasaki §10.2.1)

Seventeenth layer (PR17) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR1 introduced the spin-reflection coefficient matrix `spinReflectionCoeff` (the
interleaved/spinful coefficient matrix, with the down index read as a hole) on which
the SRP positivity `spinReflection_gramMatrix_nonneg` lives, and PR6/PR10 the block
coefficient matrix `hubbardBlockCoeff` on which the kinetic acts as `C ↦ A·C + C·Bᵣ`.
This file connects them through the signed permutation operator
`U = hubbardBlockToSpinfulPermutationOperator N`.

Because both matrices use the **same** particle-hole hole gauge and differ only by
interleaved vs block merge (related by `hubbardBlockToSpinfulConfigEquiv`), the bridge
is *entrywise*: a per-configuration Jordan–Wigner sign — **not** a row/column gauge —
multiplies the block coefficient matrix:

  `spinReflectionCoeff (U ψ) u h = ε(π, block-merge) · hubbardBlockCoeff ψ u h`,

with `ε = translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N)`.  (The sign is not
row/column-factorable, so it cannot transport positive-semidefiniteness; the RP energy
form is therefore carried on the *raw* `hubbardBlockCoeff`.)

## Main results

* `permutationOperator_mulVec_apply` — the value of a signed-permutation-operator
  action on an arbitrary vector: `(U ψ) τ = ε(π, τ∘π) · ψ (τ∘π)`.
* `spinReflectionCoeff_hubbardBlockToSpinfulPermutationOperator_mulVec` — the bridge.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The value of the signed permutation operator acting on an arbitrary vector:
`(permutationOperator π · ψ) τ = ε(π, τ∘π) · ψ (τ∘π)`.  The only surviving column in
`∑_σ (U)_{τ,σ} ψ_σ` is `σ = τ∘π` (the one with `τ = σ∘π⁻¹`). -/
theorem permutationOperator_mulVec_apply (π : Equiv.Perm (Fin (M + 1)))
    (ψ : (Fin (M + 1) → Fin 2) → ℂ) (τ : Fin (M + 1) → Fin 2) :
    (permutationOperator π).mulVec ψ τ = translationJwSign π (τ ∘ π) * ψ (τ ∘ π) := by
  change ∑ σ : Fin (M + 1) → Fin 2, permutationOperator π τ σ * ψ σ
      = translationJwSign π (τ ∘ π) * ψ (τ ∘ π)
  rw [Finset.sum_eq_single (τ ∘ π)]
  · rw [permutationOperator, Matrix.of_apply,
      if_pos (by rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id])]
  · intro σ _ hσ
    have hne : ¬ (τ = σ ∘ (π : Equiv.Perm (Fin (M + 1))).symm) := by
      intro heq
      apply hσ
      rw [heq, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    rw [permutationOperator, Matrix.of_apply, if_neg hne, zero_mul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- **The SRP ↔ block coefficient bridge.**  Conjugating a state by the block ↔
interleaved permutation operator relates its spin-reflection coefficient matrix to its
block coefficient matrix entrywise, up to the per-configuration Jordan–Wigner sign of
the relabeling:
`spinReflectionCoeff (U ψ) u h = ε(π, block-merge u h) · hubbardBlockCoeff ψ u h`. -/
theorem spinReflectionCoeff_hubbardBlockToSpinfulPermutationOperator_mulVec (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    spinReflectionCoeff N ((hubbardBlockToSpinfulPermutationOperator N).mulVec ψ)
      = fun u h =>
          translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N)
              (hubbardBlockMergeConfig N u (particleHoleConfig N h))
            * hubbardBlockCoeff N ψ u h := by
  funext u h
  -- `intMerge ∘ orbital = blockMerge`
  have hmrg : hubbardMergeConfig N u (particleHoleConfig N h)
        ∘ (hubbardBlockToSpinfulOrbitalEquiv N)
      = hubbardBlockMergeConfig N u (particleHoleConfig N h) := by
    have h1 : hubbardBlockMergeConfig N u (particleHoleConfig N h)
          ∘ (hubbardBlockToSpinfulOrbitalEquiv N).symm
        = hubbardMergeConfig N u (particleHoleConfig N h) :=
      hubbardBlockToSpinfulConfigEquiv_hubbardBlockMergeConfig N u (particleHoleConfig N h)
    rw [← h1, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [spinReflectionCoeff, hubbardBlockToSpinfulPermutationOperator,
    permutationOperator_mulVec_apply, hmrg, hubbardBlockCoeff]

end LatticeSystem.Fermion
