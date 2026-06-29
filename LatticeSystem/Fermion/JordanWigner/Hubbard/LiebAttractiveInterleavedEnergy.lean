import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveEnergyTrace
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticConj

/-!
# The interleaved kinetic energy as a block-coefficient trace (Tasaki §10.2.1)

Twenty-third layer (PR23) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

The attractive Hubbard Hamiltonian uses the interleaved kinetic operator
`hubbardKinetic`, while PR19 expressed the energy of the *block-ordered* kinetic
operator `hubbardBlockKinetic` as a trace on the block coefficient matrix. PR16
(`hubbardBlockKinetic_conj_eq`) relates the two by the signed permutation operator
`U = permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)`:
`U · hubbardBlockKinetic · Uᴴ = hubbardKinetic`. Combining this with the elementary
conjugation identity for a quadratic form, the interleaved kinetic energy of a state
`ψ` equals the PR19 block trace evaluated at the back-rotated state `Uᴴ · ψ`:

  `⟨ψ| Ĥkin |ψ⟩ = tr(C'ᴴ·(A·C' + C'·Bᵣ))`,  `C' = hubbardBlockCoeff (Uᴴ·ψ)`.

This is the kinetic half of the full attractive-Hubbard energy functional. (The
interaction is Hadamard-diagonal on the spin-reflection coefficient matrix
`spinReflectionCoeff`, which — not `hubbardBlockCoeff` — carries the
positive-semidefinite / Perron–Frobenius structure; reconciling the two coordinate
systems through the PR17 entrywise-sign bridge is a later layer.)

## Main results

* `dotProduct_conj_mul_conjTranspose` — the elementary conjugation identity
  `(star v)·((U·M·Uᴴ)·v) = (star (Uᴴ·v))·(M·(Uᴴ·v))` (pure matrix algebra).
* `hubbardKinetic_dotProduct_eq_block_trace_of_interleaved` — the interleaved
  kinetic energy as a block-coefficient trace at the back-rotated state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The conjugation identity for a quadratic form: pushing the conjugating matrix
`U` (and its adjoint) onto the test vector. Pure matrix algebra — no unitarity of
`U` is needed. -/
theorem dotProduct_conj_mul_conjTranspose {n : Type*} [Fintype n]
    (U M : Matrix n n ℂ) (v : n → ℂ) :
    dotProduct (star v) ((U * M * Uᴴ).mulVec v)
      = dotProduct (star (Uᴴ.mulVec v)) (M.mulVec (Uᴴ.mulVec v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    show (star v) ᵥ* U = star (Uᴴ.mulVec v) by
      rw [star_mulVec, Matrix.conjTranspose_conjTranspose]]

/-- **The interleaved kinetic energy as a block-coefficient trace.** The energy of
the interleaved Hubbard kinetic operator in a state `ψ` equals the PR19 block trace
evaluated at the back-rotated state `Uᴴ · ψ`, with
`U = permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)`. -/
theorem hubbardKinetic_dotProduct_eq_block_trace_of_interleaved (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) ((hubbardKinetic N T).mulVec ψ)
      = Matrix.trace
          ((hubbardBlockCoeff N
              ((permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N))ᴴ.mulVec ψ))ᴴ *
            hubbardBlockKineticCoeffAction N T
              (hubbardBlockCoeff N
                ((permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N))ᴴ.mulVec ψ))) := by
  rw [← hubbardBlockKinetic_conj_eq T, dotProduct_conj_mul_conjTranspose,
    hubbardBlockKinetic_dotProduct_eq_trace]

end LatticeSystem.Fermion
