import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticHopEntry
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKineticMatrix
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# The kinetic single-hop matrix entry is nonzero (Tasaki §10.2.4)

Layer PR40c toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The
configuration-space connectivity of the up-kinetic matrix
`A = hubbardBlockKineticUpFixedMatrix` needs: a single hop `j → i` (source occupied,
target empty) gives a **nonzero** matrix entry

  `A (hop u j i) u = (±1)·T_{i,j} ≠ 0`.

Expanding the entry over the kinetic double sum `Σ_{p,q} T_{p,q} ĉ†_{p,↑} ĉ_{q,↑}`, only
the `(p,q) = (i,j)` term reaches the hopped configuration (single-hop uniqueness, PR40b),
leaving `±T_{i,j}`.

## Main result

* `hubbardBlockKineticUpFixedMatrix_apply_hop_ne` — the single-hop entry is nonzero.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A matrix entry as the `mulVec`-on-basis component: `M a b = (M ·ᵥ |b⟩) a`. -/
private theorem opEntry_eq_mulVec {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (M : Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ) (a b : Λ → Fin 2) :
    M a b = (M.mulVec (basisVec b)) a :=
  (sum_mul_basisVec b (M a)).symm

/-- An off-target single-`(p,q)` up-hop term contributes nothing to the hopped entry:
its `mulVec`-on-basis component at `merge (hop u j i) D` vanishes unless `(p,q) = (i,j)`. -/
private theorem upHopTerm_apply_eq_zero_of_ne (u D : hubbardSpinConfig N) (i j p q : Fin (N + 1))
    (huj : u j = 1) (hui : u i = 0) (hpq : ¬(p = i ∧ q = j)) :
    ((fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N p 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N q 0)).mulVec
        (basisVec (hubbardBlockMergeConfig N u D)))
        (hubbardBlockMergeConfig N (hubbardSpinHopConfig N u j i) D) = 0 := by
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split_ifs with hcond
  · rw [Pi.smul_apply, smul_eq_mul]
    -- the hopped result config differs from `merge (hop u j i) D`.
    have hBeq : Function.update (Function.update (hubbardBlockMergeConfig N u D)
          (hubbardBlockIndex N q 0) 0) (hubbardBlockIndex N p 0) 1
        = hubbardBlockMergeConfig N (hubbardSpinHopConfig N u q p) D := by
      rw [← hubbardBlockMergeConfig_update_up, ← hubbardBlockMergeConfig_update_up,
        hubbardSpinHopConfig]
    have hne : hubbardBlockMergeConfig N (hubbardSpinHopConfig N u j i) D
        ≠ hubbardBlockMergeConfig N (hubbardSpinHopConfig N u q p) D := by
      intro hAB
      have h2 := congrArg (hubbardBlockUpConfig N) hAB
      rw [hubbardBlockUpConfig_merge, hubbardBlockUpConfig_merge] at h2
      exact hpq (hubbardSpinHopConfig_inj_of_hop u i j p q huj hui h2.symm)
    rw [hBeq, basisVec_of_ne hne, mul_zero]
  · rfl

/-- **The single-hop kinetic matrix entry is nonzero.** For symmetric occupation
`u j = 1`, `u i = 0` with `i ≠ j` and `T_{i,j} ≠ 0`, the entry of the up-kinetic matrix
between the hopped configuration `hop u j i` and `u` is nonzero. -/
theorem hubbardBlockKineticUpFixedMatrix_apply_hop_ne (u : hubbardSpinConfig N)
    (i j : Fin (N + 1)) (huj : u j = 1) (hui : u i = 0) (hij : i ≠ j)
    {T : Fin (N + 1) → Fin (N + 1) → ℂ} (hT : T i j ≠ 0) :
    hubbardBlockKineticUpFixedMatrix N T (hubbardSpinHopConfig N u j i) u ≠ 0 := by
  set D := particleHoleConfig N (fun _ : Fin (N + 1) => (0 : Fin 2)) with hD
  -- The entry is the operator matrix element = the `mulVec`-on-basis component.
  rw [hubbardBlockKineticUpFixedMatrix, hubbardBlockKineticUpCoeffMatrix,
    opEntry_eq_mulVec (hubbardBlockKineticUp N T)
      (hubbardBlockMergeConfig N (hubbardSpinHopConfig N u j i) D)
      (hubbardBlockMergeConfig N u D),
    hubbardBlockKineticUp, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_eq_single i ?_ ?_]
  · rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_eq_single j ?_ ?_]
    · -- the surviving `(i,j)` term value `= (±1)·T_{i,j} ≠ 0`.
      rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
      rcases lt_trichotomy j.val i.val with hlt | heq | hlt
      · rw [hubbardBlock_upHop_forward_mulVec N u D j i hlt huj hui,
          Pi.smul_apply, smul_eq_mul, basisVec_self, mul_one]
        exact mul_ne_zero hT (pow_ne_zero _ (by norm_num))
      · exact absurd (Fin.ext heq.symm) hij
      · rw [hubbardBlock_upHop_backward_mulVec N u D j i hlt huj hui,
          Pi.smul_apply, smul_eq_mul, basisVec_self, mul_one]
        exact mul_ne_zero hT (pow_ne_zero _ (by norm_num))
    · intro q _ hqj
      rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
        upHopTerm_apply_eq_zero_of_ne u D i j i q huj hui (fun h => hqj h.2), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hpi
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      upHopTerm_apply_eq_zero_of_ne u D i j p q huj hui (fun h => hpi h.1), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end LatticeSystem.Fermion
