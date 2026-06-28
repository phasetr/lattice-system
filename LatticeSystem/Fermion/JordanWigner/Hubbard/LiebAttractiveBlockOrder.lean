import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopSignBetween

/-!
# Block (species-separated) spin-orbital order and Jordan–Wigner sign separation (Tasaki §10.2.1)

Third layer (PR3) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

The repository's `spinfulIndex N i σ = 2 i + σ` **interleaves** up (even) and down
(odd) orbitals. In that order the Jordan–Wigner string of a same-species hop
`ĉ†_{i,σ} ĉ_{j,σ}` passes through the *opposite*-species orbitals lying between the
two positions, so the hopping sign depends on the opposite spin configuration and
the kinetic term does **not** factor as a left/right action on the
coefficient matrix. Lieb's argument needs the **block order** (all up orbitals
`0 … N`, then all down orbitals `N+1 … 2N+1`), in which a same-species hop only
crosses orbitals of its own species.

This file introduces the block index `hubbardBlockIndex N i σ = i + σ (N+1)`, the
block merge of an up/down configuration pair, and proves the **sign-separation**
lemmas: in block order the combined JW sign of an up-spin hop depends only on the
up configuration (the occupation between the two sites), and likewise the
down-spin hop depends only on the down configuration. The connection between the
block-ordered kinetic operator and the interleaved `hubbardKinetic`, and the
resulting left/right coefficient-matrix action, are subsequent layers (PR4+).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## The block (species-separated) spin-orbital index -/

/-- The block spinful index: all up orbitals first (`σ = 0 ↦ i`), then all down
orbitals (`σ = 1 ↦ i + (N+1)`). -/
def hubbardBlockIndex (N : ℕ) (i : Fin (N + 1)) (σ : Fin 2) : Fin (2 * N + 2) :=
  ⟨i.val + (if σ = 0 then 0 else N + 1), by have := i.isLt; split <;> omega⟩

@[simp]
theorem hubbardBlockIndex_zero_val (N : ℕ) (i : Fin (N + 1)) :
    (hubbardBlockIndex N i 0).val = i.val := by simp [hubbardBlockIndex]

@[simp]
theorem hubbardBlockIndex_one_val (N : ℕ) (i : Fin (N + 1)) :
    (hubbardBlockIndex N i 1).val = i.val + (N + 1) := by
  simp only [hubbardBlockIndex]
  rw [if_neg (by decide)]

/-! ## The block merge of an up/down configuration pair -/

/-- Reconstruct a spin-orbital configuration from up/down parts in block order:
positions `< N+1` carry the up part, positions `≥ N+1` carry the down part. -/
def hubbardBlockMergeConfig (N : ℕ) (u d : hubbardSpinConfig N) :
    Fin (2 * N + 2) → Fin 2 :=
  fun o =>
    if h : o.val < N + 1 then u ⟨o.val, h⟩
    else d ⟨o.val - (N + 1), by have := o.isLt; omega⟩

@[simp]
theorem hubbardBlockMergeConfig_blockIndex_zero (N : ℕ) (u d : hubbardSpinConfig N)
    (i : Fin (N + 1)) :
    hubbardBlockMergeConfig N u d (hubbardBlockIndex N i 0) = u i := by
  have hlt : (hubbardBlockIndex N i 0).val < N + 1 := by
    rw [hubbardBlockIndex_zero_val]; exact i.isLt
  rw [hubbardBlockMergeConfig, dif_pos hlt]
  congr 1

@[simp]
theorem hubbardBlockMergeConfig_blockIndex_one (N : ℕ) (u d : hubbardSpinConfig N)
    (i : Fin (N + 1)) :
    hubbardBlockMergeConfig N u d (hubbardBlockIndex N i 1) = d i := by
  have hge : ¬ (hubbardBlockIndex N i 1).val < N + 1 := by
    rw [hubbardBlockIndex_one_val]; omega
  have hval : (hubbardBlockIndex N i 1).val - (N + 1) = i.val := by
    rw [hubbardBlockIndex_one_val]; omega
  rw [hubbardBlockMergeConfig, dif_neg hge]
  congr 1
  exact Fin.ext hval

/-- On an up orbital (`o.val < N+1`) the block merge reads the up part. -/
theorem hubbardBlockMergeConfig_of_lt (N : ℕ) (u d : hubbardSpinConfig N)
    (o : Fin (2 * N + 2)) (h : o.val < N + 1) :
    hubbardBlockMergeConfig N u d o = u ⟨o.val, h⟩ := dif_pos h

/-- On a down orbital (`N+1 ≤ o.val`) the block merge reads the down part. -/
theorem hubbardBlockMergeConfig_of_ge (N : ℕ) (u d : hubbardSpinConfig N)
    (o : Fin (2 * N + 2)) (h : ¬ o.val < N + 1) :
    hubbardBlockMergeConfig N u d o =
      d ⟨o.val - (N + 1), by have := o.isLt; omega⟩ := dif_neg h

/-! ## Jordan–Wigner sign separation in block order -/

/-- **The between-occupation of an up-orbital hop depends only on the up
configuration.** Reindexing the block-order modes strictly between two up
orbitals `j, i` to the up sites between `j` and `i`. -/
theorem hubbardBlock_betweenSum_up (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) :
    (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter
        (fun k => (hubbardBlockIndex N j 0).val < k.val ∧
          k.val < (hubbardBlockIndex N i 0).val), (hubbardBlockMergeConfig N u d k).val)
      = ∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (u k).val := by
  simp only [hubbardBlockIndex_zero_val]
  refine Finset.sum_bij'
    (fun k hk => (⟨k.val, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have := i.isLt; omega⟩ : Fin (N + 1)))
    (fun k _ => (⟨k.val, by have := k.isLt; omega⟩ : Fin (2 * N + 2)))
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have := i.isLt; omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; omega
  · intro k _; rfl
  · intro k _; rfl
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hubbardBlockMergeConfig_of_lt N u d k (by have := i.isLt; omega)]

/-- **The between-occupation of a down-orbital hop depends only on the down
configuration.** -/
theorem hubbardBlock_betweenSum_down (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) :
    (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter
        (fun k => (hubbardBlockIndex N j 1).val < k.val ∧
          k.val < (hubbardBlockIndex N i 1).val), (hubbardBlockMergeConfig N u d k).val)
      = ∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (d k).val := by
  simp only [hubbardBlockIndex_one_val]
  refine Finset.sum_bij'
    (fun k hk => (⟨k.val - (N + 1), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have := i.isLt; omega⟩ : Fin (N + 1)))
    (fun k _ => (⟨k.val + (N + 1), by have := k.isLt; omega⟩ : Fin (2 * N + 2)))
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have := i.isLt; omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have h : k.val - (N + 1) + (N + 1) = k.val := by omega
    exact Fin.ext h
  · intro k _
    have h : k.val + (N + 1) - (N + 1) = k.val := by omega
    exact Fin.ext h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hubbardBlockMergeConfig_of_ge N u d k (by omega)]

/-- **Up-hop sign separation (forward).** In block order the combined Jordan–Wigner
sign of a forward up-spin hop `j → i` (`j.val < i.val`) depends only on the up
configuration, through the occupation of the up sites strictly between `j` and `i`. -/
theorem hubbardBlock_upHop_jwSign_forward (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hji : j.val < i.val) :
    jwSign (2 * N + 1) (hubbardBlockIndex N j 0) (hubbardBlockMergeConfig N u d) *
        jwSign (2 * N + 1) (hubbardBlockIndex N i 0)
          (Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 0) 0)
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (u k).val) := by
  have hqp : (hubbardBlockIndex N j 0).val < (hubbardBlockIndex N i 0).val := by
    rw [hubbardBlockIndex_zero_val, hubbardBlockIndex_zero_val]; exact hji
  rw [jwSign_mul_jwSign_update_forward (2 * N + 1) (hubbardBlockIndex N j 0)
    (hubbardBlockIndex N i 0) (hubbardBlockMergeConfig N u d) hqp]
  rw [hubbardBlock_betweenSum_up]

/-- **Down-hop sign separation (forward).** In block order the combined Jordan–Wigner
sign of a forward down-spin hop `j → i` (`j.val < i.val`) depends only on the down
configuration. -/
theorem hubbardBlock_downHop_jwSign_forward (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hji : j.val < i.val) :
    jwSign (2 * N + 1) (hubbardBlockIndex N j 1) (hubbardBlockMergeConfig N u d) *
        jwSign (2 * N + 1) (hubbardBlockIndex N i 1)
          (Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 1) 0)
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => j.val < k.val ∧ k.val < i.val), (d k).val) := by
  have hqp : (hubbardBlockIndex N j 1).val < (hubbardBlockIndex N i 1).val := by
    rw [hubbardBlockIndex_one_val, hubbardBlockIndex_one_val]; omega
  rw [jwSign_mul_jwSign_update_forward (2 * N + 1) (hubbardBlockIndex N j 1)
    (hubbardBlockIndex N i 1) (hubbardBlockMergeConfig N u d) hqp]
  rw [hubbardBlock_betweenSum_down]

/-- **Up-hop sign separation (backward).** For a backward up-spin hop `j → i`
(`i.val < j.val`) into an empty up target (`u i = 0`), the combined Jordan–Wigner
sign depends only on the up configuration between `i` and `j`. -/
theorem hubbardBlock_upHop_jwSign_backward (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hij : i.val < j.val) (hui : u i = 0) :
    jwSign (2 * N + 1) (hubbardBlockIndex N j 0) (hubbardBlockMergeConfig N u d) *
        jwSign (2 * N + 1) (hubbardBlockIndex N i 0)
          (Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 0) 0)
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => i.val < k.val ∧ k.val < j.val), (u k).val) := by
  have hpq : (hubbardBlockIndex N i 0).val < (hubbardBlockIndex N j 0).val := by
    rw [hubbardBlockIndex_zero_val, hubbardBlockIndex_zero_val]; exact hij
  have hcp : hubbardBlockMergeConfig N u d (hubbardBlockIndex N i 0) = 0 := by
    rw [hubbardBlockMergeConfig_blockIndex_zero]; exact hui
  rw [jwSign_mul_jwSign_update_backward (2 * N + 1) (hubbardBlockIndex N j 0)
    (hubbardBlockIndex N i 0) (hubbardBlockMergeConfig N u d) hpq hcp]
  rw [hubbardBlock_betweenSum_up]

/-- **Down-hop sign separation (backward).** For a backward down-spin hop `j → i`
(`i.val < j.val`) into an empty down target (`d i = 0`), the combined Jordan–Wigner
sign depends only on the down configuration between `i` and `j`. -/
theorem hubbardBlock_downHop_jwSign_backward (N : ℕ) (u d : hubbardSpinConfig N)
    (j i : Fin (N + 1)) (hij : i.val < j.val) (hdi : d i = 0) :
    jwSign (2 * N + 1) (hubbardBlockIndex N j 1) (hubbardBlockMergeConfig N u d) *
        jwSign (2 * N + 1) (hubbardBlockIndex N i 1)
          (Function.update (hubbardBlockMergeConfig N u d) (hubbardBlockIndex N j 1) 0)
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
          (fun k => i.val < k.val ∧ k.val < j.val), (d k).val) := by
  have hpq : (hubbardBlockIndex N i 1).val < (hubbardBlockIndex N j 1).val := by
    rw [hubbardBlockIndex_one_val, hubbardBlockIndex_one_val]; omega
  have hcp : hubbardBlockMergeConfig N u d (hubbardBlockIndex N i 1) = 0 := by
    rw [hubbardBlockMergeConfig_blockIndex_one]; exact hdi
  rw [jwSign_mul_jwSign_update_backward (2 * N + 1) (hubbardBlockIndex N j 1)
    (hubbardBlockIndex N i 1) (hubbardBlockMergeConfig N u d) hpq hcp]
  rw [hubbardBlock_betweenSum_down]

end LatticeSystem.Fermion
