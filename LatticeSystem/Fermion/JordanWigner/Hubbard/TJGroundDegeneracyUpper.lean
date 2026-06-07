import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightReindex

/-!
# Tasaki 11.5: degeneracy upper bound `finrank G ≤ Ne+1` (Prop 11.24 E5b)

Assembling the finite `Ŝ³` weight decomposition `G = ⨆ a : Fin (Ne+1), G ⊓ eigenspace Ŝ³ (a − Ne/2)`
(`tJ_groundSubmodule_eq_iSup_weight`) with the per-weight-block bound
(`tJ_ground_weight_finrank_le_one_pos/_neg`, every half-integer block is `≤ 1`-dimensional) gives
the ground-state degeneracy upper bound:

* `tJ_groundSubmodule_finrank_le` — `finrank G ≤ Ne+1`.

The `Ŝ³` eigenspaces are independent (`Module.End.eigenspaces_iSupIndep`), so the weight blocks form
an internal direct sum of `G`; `finrank G = ∑ finrank (block) ≤ (Ne+1)·1`.

Paired with the SU(2)-tower lower bound `Ne+1 ≤ finrank G` (`tJ_groundSubmodule_finrank_ge`), this
pins `finrank G = Ne+1`, the input to the maximal-spin multiplet capstone (E6).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **Degeneracy upper bound.**  `finrank G ≤ Ne+1` for the t-J ground subspace at odd filling `Ne`:
the `Ne+1` half-integer `Ŝ³` weight blocks form an internal direct sum of `G`
(`tJ_groundSubmodule_eq_iSup_weight` + `eigenspaces_iSupIndep`), and each block is `≤ 1`-dimensional
(`tJ_ground_weight_finrank_le_one_pos/_neg`), so `finrank G = ∑ finrank (block) ≤ Ne+1`. -/
theorem tJ_groundSubmodule_finrank_le (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne) ≤
      Ne + 1 := by
  classical
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne with hG
  set T := (fermionTotalSpinZ N).mulVecLin with hT
  set wt : Fin (Ne + 1) → ℂ := fun a => (((a : ℝ) - (Ne : ℝ) / 2 : ℝ) : ℂ) with hwt
  set B : Fin (Ne + 1) → Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
    fun a => G ⊓ Module.End.eigenspace T (wt a) with hB
  have hsup : ⨆ a, B a = G :=
    (tJ_groundSubmodule_eq_iSup_weight N Ne (cycleGraph (N + 1)) τ J).symm
  -- the weight values are distinct
  have hwt_inj : Function.Injective wt := by
    intro a a' h
    simp only [hwt] at h
    have hr : ((a : ℝ) - (Ne : ℝ) / 2) = ((a' : ℝ) - (Ne : ℝ) / 2) := by exact_mod_cast h
    exact Fin.ext (by exact_mod_cast (by linarith : (a : ℝ) = (a' : ℝ)))
  -- the weight blocks are independent (sub-family of the independent Ŝ³ eigenspaces)
  have hindep : iSupIndep B :=
    ((Module.End.eigenspaces_iSupIndep T).comp hwt_inj).mono (fun a => inf_le_right)
  -- the blocks form an internal direct sum of G
  have hinj : Function.Injective (DirectSum.coeLinearMap B) := hindep.dfinsupp_lsum_injective
  have hrange : LinearMap.range (DirectSum.coeLinearMap B) = G := by
    rw [DirectSum.range_coeLinearMap]; exact hsup
  have hfr : finrank ℂ ↥G = ∑ a, finrank ℂ ↥(B a) := by
    rw [← hrange, ← (LinearEquiv.ofInjective (DirectSum.coeLinearMap B) hinj).finrank_eq,
      Module.finrank_directSum]
  -- each block is at most one-dimensional
  have hblock : ∀ a, finrank ℂ ↥(B a) ≤ 1 := by
    intro a
    obtain ⟨m, hm⟩ := hodd
    change finrank ℂ ↥(G ⊓ Module.End.eigenspace T (wt a)) ≤ 1
    rcases Nat.lt_or_ge (a : ℕ) (m + 1) with hlt | hge
    · obtain ⟨k, hk⟩ : ∃ k, (a : ℕ) + k = m := ⟨m - (a : ℕ), by omega⟩
      have heq : wt a = (((-(1 / 2) - (k : ℕ) : ℝ)) : ℂ) := by
        simp only [hwt]; rw [Complex.ofReal_inj]
        have ha : (a : ℝ) = (m : ℝ) - (k : ℝ) := by
          have hc : ((a : ℕ) : ℝ) + (k : ℝ) = (m : ℝ) := by exact_mod_cast hk
          have he : ((a : ℕ) : ℝ) = (a : ℝ) := rfl
          linarith
        rw [ha, show (Ne : ℝ) = 2 * (m : ℝ) + 1 by exact_mod_cast hm]; ring
      rw [heq, hG, hT]
      exact tJ_ground_weight_finrank_le_one_neg hpos Ne hNeLt ⟨m, hm⟩ τ J hτ hJ k
    · obtain ⟨k, hk⟩ : ∃ k, (a : ℕ) = m + 1 + k := ⟨(a : ℕ) - (m + 1), by omega⟩
      have heq : wt a = (((1 / 2 + (k : ℕ) : ℝ)) : ℂ) := by
        simp only [hwt]; rw [Complex.ofReal_inj]
        have ha : (a : ℝ) = (m : ℝ) + 1 + (k : ℝ) := by exact_mod_cast hk
        rw [ha, show (Ne : ℝ) = 2 * (m : ℝ) + 1 by exact_mod_cast hm]; ring
      rw [heq, hG, hT]
      exact tJ_ground_weight_finrank_le_one_pos hpos Ne hNeLt ⟨m, hm⟩ τ J hτ hJ k
  rw [hfr]
  calc ∑ a, finrank ℂ ↥(B a) ≤ ∑ _a : Fin (Ne + 1), 1 := Finset.sum_le_sum (fun a _ => hblock a)
    _ = Ne + 1 := by simp

end LatticeSystem.Fermion
