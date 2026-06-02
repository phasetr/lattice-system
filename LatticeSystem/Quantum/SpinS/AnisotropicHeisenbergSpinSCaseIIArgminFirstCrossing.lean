import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergArgminExtraction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSInfMem
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIStrictGapFromCrossing

/-!
# General spin-S case-(ii) target bridge from an argmin first crossing

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4102 exposed a callback at the first crossing of each non-balanced
magnetization sector.  This file narrows that callback to the sector selected
by the existing argmin extraction over first-crossing times.  The remaining
case-(ii) mathematical input can therefore assume the chosen sector minimises
the first crossing among all non-balanced sectors with non-empty crossing set.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
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

/-! ## Case-(ii) target wrappers from an argmin first-crossing callback -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from an
argmin first-crossing callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_argmin_first_crossing
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_argmin_first_crossing_contradiction :
      caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne htarget_crossing => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_argmin_first_crossing_contradiction M hM_ne (by
          simpa [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath]
            using htarget_crossing))

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from an argmin first-crossing callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_argmin_first_crossing
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_argmin_first_crossing_contradiction :
      caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne htarget_crossing => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_argmin_first_crossing_contradiction M hM_ne (by
          simpa [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath]
            using htarget_crossing))
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
