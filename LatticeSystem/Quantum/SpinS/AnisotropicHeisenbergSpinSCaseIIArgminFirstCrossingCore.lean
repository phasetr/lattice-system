import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergArgminExtraction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSInfMem

/-!
# Case (ii) argmin first-crossing: crossing contradiction (foundation)

Foundational layer extracted from `AnisotropicHeisenbergSpinSCaseIIArgminFirstCrossing.lean` for
build speed.  This file proves the target crossing contradiction from an argmin first-crossing
callback.

The case-(ii) target wrappers from an argmin first-crossing callback are kept in the capstone module
`AnisotropicHeisenbergSpinSCaseIIArgminFirstCrossing.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Target crossing contradiction from an argmin first-crossing callback -/

/-- **Argmin first-crossing contradiction callback** for general spin-`S`
case (ii).

The callback only has to contradict the sector chosen by the finite argmin
extraction: `M_chosen` has a non-empty crossing set, lies in the valid
magnetization range, is not the balanced sector, and minimises the `sInf`
first-crossing time among all non-balanced sectors with non-empty crossing
set. -/
def caseIIArgminFirstCrossingContradiction
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (lam D : ℝ) : Prop :=
  ∀ M_chosen : ℕ, ∀ _ : Nonempty (magConfigS Λ N M_chosen),
    M_chosen ∈ Finset.range (Fintype.card Λ * N + 1) →
    M_chosen ≠ M_balanced →
    (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
      Icc (0 : ℝ) 1).Nonempty →
    (∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam D ∩
        Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam D ∩
        Icc (0 : ℝ) 1)) →
    ∀ t_first : ℝ,
      t_first =
          sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
            Icc (0 : ℝ) 1) →
      t_first ∈
          perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
            Icc (0 : ℝ) 1 →
      False

/-- **General spin-S case-(ii) target crossing contradiction from an argmin
first-crossing callback**.

A target crossing gives a non-empty crossing set at `t = 1`.  The existing
finite argmin extraction chooses a sector whose first crossing is minimal
among all non-balanced non-empty crossing sectors.  It is therefore enough for
the remaining contradiction callback to handle that chosen argmin sector,
rather than every sector separately. -/
theorem anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_argmin_first_crossing_contradiction :
      caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D)
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M lam D 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 1 →
    False := by
  classical
  intro htarget_crossing
  have hne_orig :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
        Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, htarget_crossing, ⟨by norm_num, le_refl _⟩⟩
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star N M_balanced M hM_ne lam D hne_orig
  haveI := hM_chosen_NE
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  have h_argmin :
      ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam D ∩
          Icc (0 : ℝ) 1).Nonempty →
        sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
          Icc (0 : ℝ) 1) ≤
        sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam D ∩
          Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star N M_balanced M' lam D ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total :=
      h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  have h_first_mem :
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
        Icc (0 : ℝ) 1) ∈
      perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
        Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem
      hJ_star N M_balanced M_chosen lam D hM_chosen_cross
  exact h_argmin_first_crossing_contradiction
    M_chosen inferInstance hM_chosen_range hM_chosen_ne_bal hM_chosen_cross
    h_argmin
    (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam D ∩
      Icc (0 : ℝ) 1))
    rfl h_first_mem

end LatticeSystem.Quantum
