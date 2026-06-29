import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCocycleOperator
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKineticMatrix

/-!
# The block ↔ interleaved kinetic operator equality (Tasaki §10.2.1)

Sixteenth layer (PR16) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR15 proved the single-hop conjugation identity `U (ĉ†_p ĉ_q) Uᴴ = ĉ†_{π p} ĉ_{π q}`
for the signed permutation operator `U = permutationOperator π`.  Summing it over the
hopping matrix, with `π = hubbardBlockToSpinfulOrbitalEquiv N` the block ↔ interleaved
orbital relabeling, gives the **kinetic operator equality**

  `U · hubbardBlockKinetic · Uᴴ = hubbardKinetic`,

i.e. the unitary `U` carries the block-ordered kinetic operator `Ĥ↑ + Ĥ↓` to the
interleaved (spinful) Hubbard kinetic operator.  This is the operator-level statement
that the two orderings are unitarily equivalent.

## Main results

* `hubbardBlockKineticSpecies_conj_eq` — per-species conjugation: the conjugated
  single-species block kinetic sum equals the interleaved single-species kinetic sum.
* `hubbardBlockKinetic_conj_eq` — `U · hubbardBlockKinetic · Uᴴ = hubbardKinetic`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Per-species conjugation.**  Conjugating the single-species block kinetic sum
`Σ_{i,j} T_{ij} ĉ†_{block i s} ĉ_{block j s}` by `U = permutationOperator π` (with
`π` the block ↔ interleaved relabeling) yields the interleaved single-species sum
`Σ_{i,j} T_{ij} ĉ†_{spinful i s} ĉ_{spinful j s}`.  Each summand is handled by the
PR15 single-hop identity, with the orbital permutation sending `block i s` to
`spinful i s`. -/
theorem hubbardBlockKineticSpecies_conj_eq (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (s : Fin 2) :
    (permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)) *
        (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), T i j •
          (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i s) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j s))) *
        (permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N))ᴴ
      = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), T i j •
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N i s) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j s)) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    permutationOperator_hop_conj_eq, hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex]

/-- **The block ↔ interleaved kinetic operator equality.**  The signed permutation
operator `U = permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)` conjugates the
block-ordered spin-symmetric kinetic operator `Ĥ↑ + Ĥ↓` to the interleaved Hubbard
kinetic operator: `U · hubbardBlockKinetic · Uᴴ = hubbardKinetic`. -/
theorem hubbardBlockKinetic_conj_eq (T : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N)) *
        (hubbardBlockKinetic N T) *
        (permutationOperator (hubbardBlockToSpinfulOrbitalEquiv N))ᴴ
      = hubbardKinetic N T := by
  rw [hubbardBlockKinetic, Matrix.mul_add, Matrix.add_mul, hubbardBlockKineticUp,
    hubbardBlockKineticDown, hubbardBlockKineticSpecies_conj_eq T 0,
    hubbardBlockKineticSpecies_conj_eq T 1, hubbardKinetic, Fin.sum_univ_two]

end LatticeSystem.Fermion
