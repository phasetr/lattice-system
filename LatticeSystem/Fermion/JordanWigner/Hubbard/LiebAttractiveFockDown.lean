import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFockUp
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeffDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore

/-!
# Gauge independence of the down-kinetic coefficient matrix (Tasaki §10.2.1)

Ninth layer (PR9) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

This is the **down-spin dual** of PR8 (`LiebAttractiveFockUp.lean`): the per-row
matrix `hubbardBlockKineticDownCoeffMatrix N T u` is shown to be **independent of
the up label `u`**. Unlike the up case, an individual Jordan–Wigner sign at a down
block index sees *all* up orbitals (they lie below it), so the individual down sign
depends on the up configuration; only the **combined** hop sign is up-independent
(the up contribution appears squared and cancels). We therefore reuse the PR4
single-hop action lemmas (whose combined sign is already down-only) via a
`lt_trichotomy` case split.

## Main results

* `basisVec_hubbardBlockMerge_same_up_eq` — a basis-vector value between two
  block-merge configs with a common up part is independent of that up part.
* `hubbardBlock_downHop_apply_merge_indep_up` — the single down-hop matrix entry
  between configs with a common up part is independent of that up part.
* `hubbardBlockKineticDown_apply_merge_indep_up` /
  `hubbardBlockKineticDownCoeffMatrix_indep_up` — the down-kinetic matrix entry
  and the per-row coefficient matrix are independent of the up configuration.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A basis-vector value between two block-merge configs sharing an up part is
independent of that up part (it is `1` iff the down parts agree). -/
theorem basisVec_hubbardBlockMerge_same_up_eq (N : ℕ) (x y u u' : hubbardSpinConfig N) :
    basisVec (hubbardBlockMergeConfig N u x) (hubbardBlockMergeConfig N u y)
      = basisVec (hubbardBlockMergeConfig N u' x) (hubbardBlockMergeConfig N u' y) := by
  simp only [basisVec_apply]
  have key : ∀ w : hubbardSpinConfig N,
      (hubbardBlockMergeConfig N w y = hubbardBlockMergeConfig N w x) ↔ y = x := by
    intro w
    constructor
    · intro h; simpa using congrArg (hubbardBlockDownConfig N) h
    · intro h; rw [h]
  by_cases hyx : y = x
  · rw [if_pos ((key u).mpr hyx), if_pos ((key u').mpr hyx)]
  · rw [if_neg (fun h => hyx ((key u).mp h)), if_neg (fun h => hyx ((key u').mp h))]

/-- The matrix entry of a single down hop between configs sharing an up part is
independent of that up part. -/
theorem hubbardBlock_downHop_apply_merge_indep_up (N : ℕ) (i j : Fin (N + 1))
    (a b u u' : hubbardSpinConfig N) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
          fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
        (hubbardBlockMergeConfig N u a) (hubbardBlockMergeConfig N u b)
      = (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
          fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
        (hubbardBlockMergeConfig N u' a) (hubbardBlockMergeConfig N u' b) := by
  have e : ∀ U : hubbardSpinConfig N,
      (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
          (hubbardBlockMergeConfig N U a) (hubbardBlockMergeConfig N U b)
        = ((fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1)).mulVec
            (basisVec (hubbardBlockMergeConfig N U b)))
          (hubbardBlockMergeConfig N U a) := by
    intro U
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_mul_basisVec (hubbardBlockMergeConfig N U b)
      (fun k => (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))
        (hubbardBlockMergeConfig N U a) k)]
  rw [e u, e u']
  rcases eq_or_ne i j with rfl | hij
  · -- i = j: the hop is the number operator at `block i 1`
    rw [show (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N i 1))
        = fermionMultiNumber (2 * N + 1) (hubbardBlockIndex N i 1) from rfl,
      fermionMultiNumber_mulVec_basisVec, fermionMultiNumber_mulVec_basisVec]
    simp only [Pi.smul_apply, smul_eq_mul, hubbardBlockMergeConfig_blockIndex_one]
    rw [basisVec_hubbardBlockMerge_same_up_eq N b a u u']
  · have hbij : hubbardBlockIndex N i 1 ≠ hubbardBlockIndex N j 1 :=
      fun h => hij ((hubbardBlockIndex_one_inj N i j).mp h)
    by_cases hbj : b j = 1
    · by_cases hbi : b i = 0
      · rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h).symm) with hji | hij'
        · rw [hubbardBlock_downHop_forward_mulVec N u b j i hji hbj hbi,
            hubbardBlock_downHop_forward_mulVec N u' b j i hji hbj hbi]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [basisVec_hubbardBlockMerge_same_up_eq N (hubbardSpinHopConfig N b j i) a u u']
        · rw [hubbardBlock_downHop_backward_mulVec N u b j i hij' hbj hbi,
            hubbardBlock_downHop_backward_mulVec N u' b j i hij' hbj hbi]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [basisVec_hubbardBlockMerge_same_up_eq N (hubbardSpinHopConfig N b j i) a u u']
      · -- target occupied (`b i = 1`): the hop vanishes
        rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
          fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
          if_neg (fun hc => hbi (by
            have h2 := hc.2
            rwa [Function.update_of_ne hbij, hubbardBlockMergeConfig_blockIndex_one] at h2)),
          if_neg (fun hc => hbi (by
            have h2 := hc.2
            rwa [Function.update_of_ne hbij, hubbardBlockMergeConfig_blockIndex_one] at h2))]
        rfl
    · -- source empty (`b j = 0`): the hop vanishes
      rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
        fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
        if_neg (fun hc => hbj (by
          have h1 := hc.1
          rwa [hubbardBlockMergeConfig_blockIndex_one] at h1)),
        if_neg (fun hc => hbj (by
          have h1 := hc.1
          rwa [hubbardBlockMergeConfig_blockIndex_one] at h1))]
      rfl

/-- The down-kinetic matrix entry between configs sharing fixed down parts is
independent of the common up configuration. -/
theorem hubbardBlockKineticDown_apply_merge_indep_up (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (a b u u' : hubbardSpinConfig N) :
    (hubbardBlockKineticDown N T)
        (hubbardBlockMergeConfig N u a) (hubbardBlockMergeConfig N u b)
      = (hubbardBlockKineticDown N T)
        (hubbardBlockMergeConfig N u' a) (hubbardBlockMergeConfig N u' b) := by
  simp only [hubbardBlockKineticDown, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hubbardBlock_downHop_apply_merge_indep_up N i j a b u u']

/-- **The down-kinetic per-row coefficient matrix is independent of the up label.**
Hence the down kinetic operator acts on the block coefficient matrix as right
multiplication by a single fixed matrix. -/
theorem hubbardBlockKineticDownCoeffMatrix_indep_up (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (u u' : hubbardSpinConfig N) :
    hubbardBlockKineticDownCoeffMatrix N T u = hubbardBlockKineticDownCoeffMatrix N T u' := by
  funext h h'
  exact hubbardBlockKineticDown_apply_merge_indep_up N T
    (particleHoleConfig N h) (particleHoleConfig N h') u u'

end LatticeSystem.Fermion
