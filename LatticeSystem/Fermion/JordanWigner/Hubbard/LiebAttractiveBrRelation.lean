import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKineticMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore

/-!
# The down/up kinetic adjoint relation `Bᵣ = P·Aᵀ·P` (Tasaki §10.2.1)

Eighteenth layer (PR18) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

By the PR10 milestone the block kinetic operator acts on the block coefficient
matrix `C` as `C ↦ A·C + C·Bᵣ`, with the gauge-independent fixed matrices
`A = hubbardBlockKineticUpFixedMatrix` and
`Bᵣ = hubbardBlockKineticDownFixedRightMatrix`. Before assembling the
reflection-positive energy trace (PR19+) we fix the relation between the right
multiplier `Bᵣ` and the left multiplier `A`, so that the correct adjoint enters
the trace form. The relation, valid for *any* hopping matrix `T` (no symmetry
hypotheses), is

  `Bᵣ h h' = A (P h') (P h)`,  i.e.  `Bᵣ = P·Aᵀ·P`,

where `P = particleHoleConfig` is the particle–hole involution.

The heart is a spin-species swap of the kinetic *matrix entry*: the down-kinetic
entry between two block-merge configurations with a fixed up spectator equals the
up-kinetic entry with the two spin species exchanged (and a fixed down spectator).
The entry is independent of the spectator species because the Jordan–Wigner
between-occupation sign only sees the active species (PR3
`hubbardBlock_betweenSum_up/_down`); the diagonal `i = j` term is the same
number-operator value; and the firing condition only depends on the active
column configuration.

## Main results

* `hubbardBlock_kineticDown_entry_eq_kineticUp_entry` — the spectator-independent,
  species-symmetric kinetic matrix entry equality.
* `hubbardBlockKineticDownFixedRightMatrix_eq_up` — `Bᵣ h h' = A (P h') (P h)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A matrix entry as a coordinate of the matrix-vector product against the
standard basis vector of the column index. -/
private theorem entry_eq_mulVec_basisVec {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (M : Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ) (r c : Λ → Fin 2) :
    M r c = (M.mulVec (basisVec c)) r := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_mul_basisVec c (M r)]

/-- Swapping the spectator species in a `basisVec` value between block-merge
configurations: both equal `if q = p then 1 else 0`. -/
private theorem basisVec_merge_swap (N : ℕ) (p q w v : hubbardSpinConfig N) :
    basisVec (hubbardBlockMergeConfig N w p) (hubbardBlockMergeConfig N w q)
      = basisVec (hubbardBlockMergeConfig N p v) (hubbardBlockMergeConfig N q v) := by
  rw [basisVec_apply, basisVec_apply]
  have h1 : (hubbardBlockMergeConfig N w q = hubbardBlockMergeConfig N w p) ↔ q = p :=
    ⟨fun h => by
      have := congrArg (hubbardBlockDownConfig N) h
      rwa [hubbardBlockDownConfig_merge, hubbardBlockDownConfig_merge] at this,
      fun h => by rw [h]⟩
  have h2 : (hubbardBlockMergeConfig N q v = hubbardBlockMergeConfig N p v) ↔ q = p :=
    ⟨fun h => by
      have := congrArg (hubbardBlockUpConfig N) h
      rwa [hubbardBlockUpConfig_merge, hubbardBlockUpConfig_merge] at this,
      fun h => by rw [h]⟩
  simp only [h1, h2]

/-- **The down-kinetic single-hop matrix entry equals the up-kinetic entry with
the spin species exchanged.** The entry between block-merge configurations is
independent of the spectator species (`w` for down, `v` for up): the firing
condition and the Jordan–Wigner sign only see the active column configuration. -/
private theorem hubbardBlock_hop_entry_swap (i j : Fin (N + 1))
    (a b w v : hubbardSpinConfig N) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
        (hubbardBlockMergeConfig N w a) (hubbardBlockMergeConfig N w b)
      = (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
        (hubbardBlockMergeConfig N a v) (hubbardBlockMergeConfig N b v) := by
  rw [entry_eq_mulVec_basisVec
      (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
      (hubbardBlockMergeConfig N w a) (hubbardBlockMergeConfig N w b),
    entry_eq_mulVec_basisVec
      (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
      (hubbardBlockMergeConfig N a v) (hubbardBlockMergeConfig N b v)]
  by_cases hij : i = j
  · -- Diagonal: both sides are the number operator `n̂_i`.
    subst hij
    rw [show fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N i 1)
          = fermionMultiNumber (2 * N + 1) (hubbardBlockIndex N i 1) from rfl,
      show fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N i 0)
          = fermionMultiNumber (2 * N + 1) (hubbardBlockIndex N i 0) from rfl,
      fermionMultiNumber_mulVec_basisVec, fermionMultiNumber_mulVec_basisVec,
      Pi.smul_apply, Pi.smul_apply, hubbardBlockMergeConfig_blockIndex_one,
      hubbardBlockMergeConfig_blockIndex_zero, smul_eq_mul, smul_eq_mul]
    rw [basisVec_merge_swap N b a w v]
  · -- Off-diagonal: a genuine hop, identical firing condition and sign.
    have hnei1 : hubbardBlockIndex N i 1 ≠ hubbardBlockIndex N j 1 :=
      fun h => hij ((hubbardBlockIndex_one_inj N i j).mp h)
    have hnei0 : hubbardBlockIndex N i 0 ≠ hubbardBlockIndex N j 0 :=
      fun h => hij ((hubbardBlockIndex_zero_inj N i j).mp h)
    have hread_d : Function.update (hubbardBlockMergeConfig N w b)
        (hubbardBlockIndex N j 1) 0 (hubbardBlockIndex N i 1) = b i := by
      rw [Function.update_of_ne hnei1, hubbardBlockMergeConfig_blockIndex_one]
    have hread_u : Function.update (hubbardBlockMergeConfig N b v)
        (hubbardBlockIndex N j 0) 0 (hubbardBlockIndex N i 0) = b i := by
      rw [Function.update_of_ne hnei0, hubbardBlockMergeConfig_blockIndex_zero]
    have hUd : Function.update (Function.update (hubbardBlockMergeConfig N w b)
          (hubbardBlockIndex N j 1) 0) (hubbardBlockIndex N i 1) 1
        = hubbardBlockMergeConfig N w (hubbardSpinHopConfig N b j i) := by
      rw [hubbardSpinHopConfig, ← hubbardBlockMergeConfig_update_down N w b j 0,
        ← hubbardBlockMergeConfig_update_down N w (Function.update b j 0) i 1]
    have hUu : Function.update (Function.update (hubbardBlockMergeConfig N b v)
          (hubbardBlockIndex N j 0) 0) (hubbardBlockIndex N i 0) 1
        = hubbardBlockMergeConfig N (hubbardSpinHopConfig N b j i) v := by
      rw [hubbardSpinHopConfig, ← hubbardBlockMergeConfig_update_up N b v j 0,
        ← hubbardBlockMergeConfig_update_up N (Function.update b j 0) v i 1]
    rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
      fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
    simp only [hubbardBlockMergeConfig_blockIndex_one, hubbardBlockMergeConfig_blockIndex_zero,
      hread_d, hread_u, hUd, hUu]
    by_cases hcond : b j = 1 ∧ b i = 0
    · rw [if_pos hcond, if_pos hcond, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        basisVec_merge_swap N (hubbardSpinHopConfig N b j i) a w v]
      congr 1
      rcases lt_trichotomy j.val i.val with hlt | heq | hgt
      · rw [hubbardBlock_downHop_jwSign_forward N w b j i hlt,
          hubbardBlock_upHop_jwSign_forward N b v j i hlt]
      · exact absurd (Fin.ext heq).symm hij
      · rw [hubbardBlock_downHop_jwSign_backward N w b j i hgt hcond.2,
          hubbardBlock_upHop_jwSign_backward N b v j i hgt hcond.2]
    · rw [if_neg hcond, if_neg hcond, Pi.zero_apply, Pi.zero_apply]

/-- **The spectator-independent, species-symmetric kinetic matrix entry.** The
down-kinetic operator entry between two block-merge configurations with a fixed
up spectator `w` equals the up-kinetic operator entry with the two spin species
exchanged and a fixed down spectator `v`. -/
theorem hubbardBlock_kineticDown_entry_eq_kineticUp_entry (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (a b w v : hubbardSpinConfig N) :
    hubbardBlockKineticDown N T (hubbardBlockMergeConfig N w a)
        (hubbardBlockMergeConfig N w b)
      = hubbardBlockKineticUp N T (hubbardBlockMergeConfig N a v)
        (hubbardBlockMergeConfig N b v) := by
  rw [hubbardBlockKineticDown, hubbardBlockKineticUp]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hubbardBlock_hop_entry_swap i j a b w v]

/-- **The down/up kinetic adjoint relation `Bᵣ = P·Aᵀ·P`.** The right multiplier
matrix of the down kinetic action equals the (transposed, particle-hole-conjugated)
left multiplier matrix of the up kinetic action. -/
theorem hubbardBlockKineticDownFixedRightMatrix_eq_up (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (h h' : hubbardSpinConfig N) :
    hubbardBlockKineticDownFixedRightMatrix N T h h'
      = hubbardBlockKineticUpFixedMatrix N T (particleHoleConfig N h')
          (particleHoleConfig N h) := by
  simp only [hubbardBlockKineticDownFixedRightMatrix, Matrix.transpose_apply,
    hubbardBlockKineticDownCoeffMatrix, hubbardBlockKineticUpFixedMatrix,
    hubbardBlockKineticUpCoeffMatrix]
  exact hubbardBlock_kineticDown_entry_eq_kineticUp_entry N T
    (particleHoleConfig N h') (particleHoleConfig N h) (fun _ => 0)
    (particleHoleConfig N (fun _ => 0))

end LatticeSystem.Fermion
