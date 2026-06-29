import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHopAction

/-!
# The block-order kinetic operators mix a single spin species (Tasaki §10.2.1)

Fifth layer (PR5) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

Building on the single-hop action of `LiebAttractiveHopAction.lean`, this file
defines the **block-order single-species kinetic operators**
`hubbardBlockKineticUp` / `hubbardBlockKineticDown` (the second-quantized Fock
kinetic operators of one spin species) and proves that the up kinetic operator
keeps the **down configuration fixed**, while the down kinetic operator keeps the
**up configuration fixed**. Concretely, acting on a block-merge basis state, the
up kinetic operator lands in the span of the basis states with the same down
configuration (and dually for the down kinetic operator). This is the
factorization `Ĥ = Ĥ↑ ⊗ 1 + 1 ⊗ Ĥ↓` at the level of the species fibers; the
identification of these operators as left / right multiplication on the
coefficient matrix and the connection to the interleaved `hubbardKinetic` are
subsequent layers (PR6+).

## Main definitions

* `hubbardBlockFixedDownSubmodule` / `hubbardBlockFixedUpSubmodule` — the span of
  block-merge basis states with a fixed down (resp. up) configuration.
* `hubbardBlockKineticUp` / `hubbardBlockKineticDown` — the block-order
  single-species kinetic operators `Σ_{i,j} T_{i,j} ĉ†_{i,σ} ĉ_{j,σ}`.

## Main results

* `hubbardBlock_upHop_mulVec_mem_fixedDown` / `hubbardBlock_downHop_mulVec_mem_fixedUp`
  — a single same-species hop keeps the opposite species' configuration fixed.
* `hubbardBlockKineticUp_mulVec_basisVec_mem_fixedDown` /
  `hubbardBlockKineticDown_mulVec_basisVec_mem_fixedUp` — the species kinetic
  operators keep the opposite species' configuration fixed.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## Fixed-species fibers -/

/-- The span of block-merge basis states with a fixed down configuration `d`
(the "up fiber" over `d`). -/
noncomputable def hubbardBlockFixedDownSubmodule (N : ℕ) (d : hubbardSpinConfig N) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (fun u => basisVec (hubbardBlockMergeConfig N u d)))

/-- The span of block-merge basis states with a fixed up configuration `u`
(the "down fiber" over `u`). -/
noncomputable def hubbardBlockFixedUpSubmodule (N : ℕ) (u : hubbardSpinConfig N) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (fun d => basisVec (hubbardBlockMergeConfig N u d)))

/-! ## Block-order single-species kinetic operators -/

/-- The block-order up-spin kinetic operator `Σ_{i,j} T_{i,j} ĉ†_{i,↑} ĉ_{j,↑}`. -/
noncomputable def hubbardBlockKineticUp (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    T i j • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
      fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))

/-- The block-order down-spin kinetic operator `Σ_{i,j} T_{i,j} ĉ†_{i,↓} ĉ_{j,↓}`. -/
noncomputable def hubbardBlockKineticDown (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    T i j • (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
      fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1))

/-! ## Single hops keep the opposite species fixed -/

/-- A block-order up hop keeps the down configuration fixed. -/
theorem hubbardBlock_upHop_mulVec_mem_fixedDown (N : ℕ) (u d : hubbardSpinConfig N)
    (i j : Fin (N + 1)) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      ∈ hubbardBlockFixedDownSubmodule N d := by
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split_ifs with h
  · rw [← hubbardBlockMergeConfig_update_up N u d j 0,
      ← hubbardBlockMergeConfig_update_up N (Function.update u j 0) d i 1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · exact Submodule.zero_mem _

/-- A block-order down hop keeps the up configuration fixed. -/
theorem hubbardBlock_downHop_mulVec_mem_fixedUp (N : ℕ) (u d : hubbardSpinConfig N)
    (i j : Fin (N + 1)) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 1)).mulVec
        (basisVec (hubbardBlockMergeConfig N u d))
      ∈ hubbardBlockFixedUpSubmodule N u := by
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split_ifs with h
  · rw [← hubbardBlockMergeConfig_update_down N u d j 0,
      ← hubbardBlockMergeConfig_update_down N u (Function.update d j 0) i 1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · exact Submodule.zero_mem _

/-! ## The species kinetic operators keep the opposite species fixed -/

/-- The block-order up kinetic operator keeps the down configuration fixed. -/
theorem hubbardBlockKineticUp_mulVec_basisVec_mem_fixedDown (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (u d : hubbardSpinConfig N) :
    (hubbardBlockKineticUp N T).mulVec (basisVec (hubbardBlockMergeConfig N u d))
      ∈ hubbardBlockFixedDownSubmodule N d := by
  rw [hubbardBlockKineticUp, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (hubbardBlock_upHop_mulVec_mem_fixedDown N u d i j)

/-- The block-order down kinetic operator keeps the up configuration fixed. -/
theorem hubbardBlockKineticDown_mulVec_basisVec_mem_fixedUp (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (u d : hubbardSpinConfig N) :
    (hubbardBlockKineticDown N T).mulVec (basisVec (hubbardBlockMergeConfig N u d))
      ∈ hubbardBlockFixedUpSubmodule N u := by
  rw [hubbardBlockKineticDown, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (hubbardBlock_downHop_mulVec_mem_fixedUp N u d i j)

end LatticeSystem.Fermion
