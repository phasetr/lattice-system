import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockOrder
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# Block-order single hops act on a single spin species (Tasaki §10.2.1)

Fourth layer (PR4) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

Building on the block (species-separated) order and the Jordan–Wigner sign
separation of `LiebAttractiveBlockOrder.lean`, this file proves that a single
same-species hop in block order acts on a block-merge basis state by updating
**only its own spin's configuration**, with the sign supplied by the PR3
separation lemma (so an up-hop only touches `u` and a down-hop only touches `d`).
This is the basis-level form of "the kinetic term factors as a left action (up)
and a right action (down) on the coefficient matrix"; assembling the block-ordered
kinetic operator and connecting it to the interleaved `hubbardKinetic` via a
signed mode-permutation operator are subsequent layers (PR5+).

## Main results

* `exists_hubbardBlockIndex` — surjectivity of the block index (deferred from PR3).
* `hubbardSpinHopConfig` — the single-particle hop `j → i` on a configuration.
* `hubbardBlockMergeConfig_update_up` / `_down` — updating the block merge at an
  up (resp. down) orbital updates only the up (resp. down) configuration.
* `hubbardBlock_upHop_forward_mulVec` / `_backward` /
  `hubbardBlock_downHop_forward_mulVec` / `_backward` — a single same-species hop
  acts on the block-merge basis state by hopping only its own spin's
  configuration, with the PR3-separated Jordan–Wigner sign.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## Block index distinctness / surjectivity -/

/-- Two up block indices coincide iff the sites coincide. -/
theorem hubbardBlockIndex_zero_inj (N : ℕ) (a b : Fin (N + 1)) :
    hubbardBlockIndex N a 0 = hubbardBlockIndex N b 0 ↔ a = b := by
  simp [Fin.ext_iff, hubbardBlockIndex]

/-- Two down block indices coincide iff the sites coincide. -/
theorem hubbardBlockIndex_one_inj (N : ℕ) (a b : Fin (N + 1)) :
    hubbardBlockIndex N a 1 = hubbardBlockIndex N b 1 ↔ a = b := by
  simp only [Fin.ext_iff, hubbardBlockIndex_one_val]; omega

/-- A down block index never equals an up block index. -/
theorem hubbardBlockIndex_one_ne_zero (N : ℕ) (a b : Fin (N + 1)) :
    hubbardBlockIndex N a 1 ≠ hubbardBlockIndex N b 0 := by
  simp only [Ne, Fin.ext_iff, hubbardBlockIndex_one_val, hubbardBlockIndex_zero_val]
  have := b.isLt; omega

/-- An up block index never equals a down block index. -/
theorem hubbardBlockIndex_zero_ne_one (N : ℕ) (a b : Fin (N + 1)) :
    hubbardBlockIndex N a 0 ≠ hubbardBlockIndex N b 1 :=
  fun h => hubbardBlockIndex_one_ne_zero N b a h.symm

/-- Every spin-orbital decomposes as a block index. -/
theorem exists_hubbardBlockIndex (N : ℕ) (k : Fin (2 * N + 2)) :
    ∃ (a : Fin (N + 1)) (r : Fin 2), k = hubbardBlockIndex N a r := by
  by_cases hlt : k.val < N + 1
  · exact ⟨⟨k.val, hlt⟩, 0, Fin.ext (by simp [hubbardBlockIndex])⟩
  · have hm : k.val - (N + 1) < N + 1 := by have := k.isLt; omega
    refine ⟨⟨k.val - (N + 1), hm⟩, 1, Fin.ext ?_⟩
    have hb : (hubbardBlockIndex N ⟨k.val - (N + 1), hm⟩ 1).val = (k.val - (N + 1)) + (N + 1) :=
      hubbardBlockIndex_one_val N ⟨k.val - (N + 1), hm⟩
    rw [hb]; omega

/-! ## Updating a block merge updates a single species -/

/-- The single-particle hop `j → i` on a configuration: empty the source `j`,
fill the target `i`. -/
def hubbardSpinHopConfig (N : ℕ) (u : hubbardSpinConfig N) (j i : Fin (N + 1)) :
    hubbardSpinConfig N :=
  Function.update (Function.update u j 0) i 1

/-- Updating the block merge at an up orbital updates only the up configuration. -/
theorem hubbardBlockMergeConfig_update_up (N : ℕ) (u d : hubbardSpinConfig N)
    (j : Fin (N + 1)) (v : Fin 2) :
    hubbardBlockMergeConfig N (Function.update u j v) d
      = Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 0) v := by
  funext o
  rcases eq_or_ne o (hubbardBlockIndex N j 0) with rfl | hne
  · rw [hubbardBlockMergeConfig_blockIndex_zero, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hne]
    by_cases ho : o.val < N + 1
    · rw [hubbardBlockMergeConfig_of_lt N _ d o ho, hubbardBlockMergeConfig_of_lt N u d o ho,
        Function.update_of_ne (fun hcontra =>
          hne (Fin.ext (by rw [hubbardBlockIndex_zero_val]; exact congrArg Fin.val hcontra)))]
    · rw [hubbardBlockMergeConfig_of_ge N _ d o ho, hubbardBlockMergeConfig_of_ge N u d o ho]

/-- Updating the block merge at a down orbital updates only the down configuration. -/
theorem hubbardBlockMergeConfig_update_down (N : ℕ) (u d : hubbardSpinConfig N)
    (j : Fin (N + 1)) (v : Fin 2) :
    hubbardBlockMergeConfig N u (Function.update d j v)
      = Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 1) v := by
  funext o
  rcases eq_or_ne o (hubbardBlockIndex N j 1) with rfl | hne
  · rw [hubbardBlockMergeConfig_blockIndex_one, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hne]
    by_cases ho : o.val < N + 1
    · rw [hubbardBlockMergeConfig_of_lt N u _ o ho, hubbardBlockMergeConfig_of_lt N u d o ho]
    · rw [hubbardBlockMergeConfig_of_ge N u _ o ho, hubbardBlockMergeConfig_of_ge N u d o ho,
        Function.update_of_ne (fun hcontra => hne (Fin.ext (by
          have h1 : o.val - (N + 1) = j.val := congrArg Fin.val hcontra
          rw [hubbardBlockIndex_one_val]; omega)))]

/-! ## A single same-species hop acts on a single spin species -/

/-- **Forward up hop in block order updates only the up configuration.** -/
theorem hubbardBlock_upHop_forward_mulVec (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hji : j.val < i.val) (huj : u j = 1) (hui : u i = 0) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (u k).val)
        • basisVec (hubbardBlockMergeConfig N (hubbardSpinHopConfig N u j i) d) := by
  have hne : hubbardBlockIndex N i 0 ≠ hubbardBlockIndex N j 0 := fun h =>
    absurd ((hubbardBlockIndex_zero_inj N i j).mp h) (fun he => by rw [he] at hji; omega)
  simp only [hubbardSpinHopConfig]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    if_pos ⟨by rw [hubbardBlockMergeConfig_blockIndex_zero]; exact huj, by
      rw [Function.update_of_ne hne, hubbardBlockMergeConfig_blockIndex_zero]; exact hui⟩,
    hubbardBlock_upHop_jwSign_forward N u d j i hji,
    ← hubbardBlockMergeConfig_update_up N u d j 0,
    ← hubbardBlockMergeConfig_update_up N (Function.update u j 0) d i 1]

/-- **Backward up hop in block order updates only the up configuration.** -/
theorem hubbardBlock_upHop_backward_mulVec (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hij : i.val < j.val) (huj : u j = 1) (hui : u i = 0) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => i.val < k.val ∧ k.val < j.val), (u k).val)
        • basisVec (hubbardBlockMergeConfig N (hubbardSpinHopConfig N u j i) d) := by
  have hne : hubbardBlockIndex N i 0 ≠ hubbardBlockIndex N j 0 := fun h =>
    absurd ((hubbardBlockIndex_zero_inj N i j).mp h) (fun he => by rw [he] at hij; omega)
  simp only [hubbardSpinHopConfig]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    if_pos ⟨by rw [hubbardBlockMergeConfig_blockIndex_zero]; exact huj, by
      rw [Function.update_of_ne hne, hubbardBlockMergeConfig_blockIndex_zero]; exact hui⟩,
    hubbardBlock_upHop_jwSign_backward N u d j i hij hui,
    ← hubbardBlockMergeConfig_update_up N u d j 0,
    ← hubbardBlockMergeConfig_update_up N (Function.update u j 0) d i 1]

/-- **Forward down hop in block order updates only the down configuration.** -/
theorem hubbardBlock_downHop_forward_mulVec (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hji : j.val < i.val) (hdj : d j = 1) (hdi : d i = 0) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (d k).val)
        • basisVec (hubbardBlockMergeConfig N u (hubbardSpinHopConfig N d j i)) := by
  have hne : hubbardBlockIndex N i 1 ≠ hubbardBlockIndex N j 1 := fun h =>
    absurd ((hubbardBlockIndex_one_inj N i j).mp h) (fun he => by rw [he] at hji; omega)
  simp only [hubbardSpinHopConfig]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    if_pos ⟨by rw [hubbardBlockMergeConfig_blockIndex_one]; exact hdj, by
      rw [Function.update_of_ne hne, hubbardBlockMergeConfig_blockIndex_one]; exact hdi⟩,
    hubbardBlock_downHop_jwSign_forward N u d j i hji,
    ← hubbardBlockMergeConfig_update_down N u d j 0,
    ← hubbardBlockMergeConfig_update_down N u (Function.update d j 0) i 1]

/-- **Backward down hop in block order updates only the down configuration.** -/
theorem hubbardBlock_downHop_backward_mulVec (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hij : i.val < j.val) (hdj : d j = 1) (hdi : d i = 0) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => i.val < k.val ∧ k.val < j.val), (d k).val)
        • basisVec (hubbardBlockMergeConfig N u (hubbardSpinHopConfig N d j i)) := by
  have hne : hubbardBlockIndex N i 1 ≠ hubbardBlockIndex N j 1 := fun h =>
    absurd ((hubbardBlockIndex_one_inj N i j).mp h) (fun he => by rw [he] at hij; omega)
  simp only [hubbardSpinHopConfig]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    if_pos ⟨by rw [hubbardBlockMergeConfig_blockIndex_one]; exact hdj, by
      rw [Function.update_of_ne hne, hubbardBlockMergeConfig_blockIndex_one]; exact hdi⟩,
    hubbardBlock_downHop_jwSign_backward N u d j i hij hdi,
    ← hubbardBlockMergeConfig_update_down N u d j 0,
    ← hubbardBlockMergeConfig_update_down N u (Function.update d j 0) i 1]

end LatticeSystem.Fermion
