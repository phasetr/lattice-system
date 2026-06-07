import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightDirectSum

/-!
# Tasaki 11.5: finite `Ŝ³` weight reindexing of the ground subspace (Prop 11.24 E5b)

The abstract decomposition `G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ`
(`tJ_groundSubmodule_eq_iSup_inf_eigenspace`) runs over all of `ℂ`, but only the `Ne+1`
half-integer values `μ = a − Ne/2` (`a = 0, …, Ne`) actually occur: a ground-subspace vector
lives in the `N̂ = Ne` shell, where the only `Ŝ³` weights are `(#↑ − #↓)/2` with `#↑ + #↓ = Ne`.

* `tJ_groundSubmodule_inf_eigenspace_eq_bot` — `G ⊓ eigenspace Ŝ³ μ = ⊥` for every `μ` outside the
  weight set `{a − Ne/2 : a ∈ Fin (Ne+1)}` (the support restriction: `N̂` and `Ŝ³` are diagonal, so
  a non-vanishing configuration must have electron number `Ne` and `Ŝ³` count `μ`, forcing `μ` into
  the set);
* `tJ_groundSubmodule_eq_iSup_weight` — `G = ⨆ a : Fin (Ne+1), G ⊓ eigenspace Ŝ³ (a − Ne/2)`,
  the finite weight decomposition feeding the degeneracy upper bound `finrank G ≤ Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **Off-weight blocks vanish.**  If `μ` is not one of the `Ne+1` half-integer weights
`a − Ne/2` (`a ∈ Fin (Ne+1)`), then `G ⊓ eigenspace Ŝ³ μ = ⊥`: a vector there is an `N̂ = Ne`
eigenstate and an `Ŝ³ = μ` eigenstate, so each supported configuration has electron number `Ne` and
`Ŝ³` count `μ = (#↑) − Ne/2`, placing `μ` in the weight set — contradiction unless the vector is
`0`. -/
theorem tJ_groundSubmodule_inf_eigenspace_eq_bot (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (μ : ℂ)
    (hμ : ∀ a : Fin (Ne + 1), μ ≠ (((a : ℝ) - (Ne : ℝ) / 2 : ℝ) : ℂ)) :
    groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvG, hveig⟩ := hv
  rw [groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at hvG
  obtain ⟨⟨_, hN⟩, _⟩ := hvG
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hveig
  funext w
  rw [Pi.zero_apply]
  by_cases hNum : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (Ne : ℂ)
  · refine mulVec_apply_eq_zero_of_spinZ_ne v μ hveig w (fun hcount => ?_)
    -- electron-number split into up/down site sums
    set aup : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with haup
    set adown : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val with hadown
    have hupC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (aup : ℂ) := by
      rw [haup, Nat.cast_sum]
    have hdownC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) = (adown : ℂ) := by
      rw [hadown, Nat.cast_sum]
    have hreindex : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (aup : ℂ) + (adown : ℂ) := by
      rw [sum_spinful_reindex N (fun k => ((w k).val : ℂ)),
        Finset.sum_congr rfl
          (fun i _ => Fin.sum_univ_two (fun r => ((w (spinfulIndex N i r)).val : ℂ))),
        Finset.sum_add_distrib, hupC, hdownC]
    have hsplitC : (aup : ℂ) + (adown : ℂ) = (Ne : ℂ) := by rw [← hreindex]; exact hNum
    have hnat : aup + adown = Ne := by exact_mod_cast hsplitC
    have hadownC : (adown : ℂ) = (Ne : ℂ) - (aup : ℂ) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplitC)
    refine hμ ⟨aup, by omega⟩ ?_
    rw [← hcount, hupC, hdownC, hadownC]
    push_cast
    ring
  · exact mulVec_apply_eq_zero_of_number_ne N v (Ne : ℂ) hN w hNum

/-- **Finite `Ŝ³` weight decomposition.**  `G = ⨆ a : Fin (Ne+1), G ⊓ eigenspace Ŝ³ (a − Ne/2)`:
the all-`ℂ` supremum collapses to the `Ne+1` occurring half-integer weights (off-weight blocks are
`⊥` by `tJ_groundSubmodule_inf_eigenspace_eq_bot`). -/
theorem tJ_groundSubmodule_eq_iSup_weight (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne =
      ⨆ a : Fin (Ne + 1), groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          (((a : ℝ) - (Ne : ℝ) / 2 : ℝ) : ℂ) := by
  refine le_antisymm ?_ (iSup_le (fun _ => inf_le_left))
  refine (tJ_groundSubmodule_eq_iSup_inf_eigenspace N Ne G τ J).le.trans (iSup_le (fun μ => ?_))
  by_cases hμ : ∃ a : Fin (Ne + 1), μ = (((a : ℝ) - (Ne : ℝ) / 2 : ℝ) : ℂ)
  · obtain ⟨a, rfl⟩ := hμ
    exact le_iSup_of_le a le_rfl
  · rw [tJ_groundSubmodule_inf_eigenspace_eq_bot N Ne G τ J μ (not_exists.mp hμ)]
    exact bot_le

end LatticeSystem.Fermion
