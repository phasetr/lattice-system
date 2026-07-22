import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedFromGlobalUniqueness
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIICorner
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIPathGlobalFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSSU2Boundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapFromGlobalUniqueness

/-!
# Case (ii): total-reachability target wrappers

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file composes the case-(ii) SU(2)-corner path-global finrank bridge with
the existing target wrappers.  The exact SU(2) corner is discharged from the
MLM/Casimir/Theorem 2.3 endpoint, and the same SU(2)-point uniqueness input
also supplies the balanced ground-sector equality and the strict non-balanced
sector gap at the start of the deformation path.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Path-global case-(ii) full `finrank <= 2` from total reachability and the
MLM/Casimir/Theorem 2.3 SU(2) endpoint. -/
theorem caseII_path_global_finrank_bound_of_total_reachability_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 := by
  classical
  have hN_one : 1 ≤ N := by omega
  have h_SU2_unique :=
    aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN_one
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
  exact caseII_path_global_finrank_bound_of_total_reachability_and_su2_unique
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself
    (caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj (Λ := Λ) A hJself hJbip)
    hJ_star hA_ne hB_ne hN hlam_case_ii hD_case_ii h_SU2_unique

/-- General spin-`S` case-(ii) target ground eigenspace `finrank <= 1` from
total reachability and the MLM/Casimir/Theorem 2.3 SU(2) endpoint. -/
theorem aHeisS_case_ii_target_finrank_le_one_of_totReach_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hN_one : 1 ≤ N := by omega
  have h_SU2_unique :=
    aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN_one
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
  have h_GS_at_SU2_base :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star N M_balanced h_balanced h_SU2_unique
  have h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2) := by
    have hpath := anisotropicHeisenbergParametricPath_zero lam D
    unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    simp only [hpath]
    exact h_GS_at_SU2_base
  have h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M lam D 0 := by
    intro M hM_nonempty hM_ne_balanced
    haveI := hM_nonempty
    have hM_range : M ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hM_nonempty
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star N M_balanced M lam D h_balanced
      (h_centered_nonzero M hM_range hM_ne_balanced)
      h_SU2_unique h_GS_at_SU2_base
  exact anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_global_finrank_bound
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN_one
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2
    (caseII_path_global_finrank_bound_of_total_reachability_and_su2_unique
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself
      (caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj (Λ := Λ) A hJself hJbip)
      hJ_star hA_ne hB_ne hN hlam_case_ii hD_case_ii h_SU2_unique)

/-- General spin-`S` case-(ii) target ground states have zero total
magnetization from total reachability and the MLM/Casimir/Theorem 2.3 SU(2)
endpoint. -/
theorem aHeisS_case_ii_target_zeroMag_of_totReach_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  have huniq :=
    aHeisS_case_ii_target_finrank_le_one_of_totReach_MLM_casLadder_t23_pf
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced h_centered_nonzero c_mlm c_toy hT23 hc_heis_strict
      hc_toy_strict h_card_eq hlam_case_ii hD_case_ii
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
