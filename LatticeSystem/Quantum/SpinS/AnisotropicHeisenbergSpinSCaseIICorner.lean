import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockReachability

/-!
# Case (ii): SU(2) corner bridge

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

The case-(ii) parity-block PF/min bridge works away from the exact SU(2)
corner `(lambda,D) = (1,0)`.  At the corner itself, the deformation argument
only needs the full ground-eigenspace `finrank <= 2` input, so this file
combines non-corner parity-block PF/min data from total reachability with a
direct full SU(2)-corner `finrank <= 1` callback.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Non-corner case-(ii) parity-block PF/min callback from bipartite complete
graph reachability totality.

The proof is the pointwise version of the case-(ii) raw-support selector: it
uses the strict consumer in the interior, the ion-only consumer on the
`lambda = 1`, `D < 0` boundary, and the bond-only consumer on the
`lambda > 1`, `D = 0` boundary.  The excluded corner branch is discharged by
`hnot_corner`. -/
theorem axisSwappedParityBlockPFMinAt_of_total_reachability_noncorner
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot_corner :
      ¬ ((anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0))
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
      (anisotropicHeisenbergParametricPath lam D t).1
      (anisotropicHeisenbergParametricPath lam D t).2 p := by
  classical
  have hN_one : 1 ≤ N := by omega
  have ht_nn : 0 ≤ t := ht.1
  have hlam_ge :
      1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 :=
    anisotropicHeisenbergParametricPath_fst_ge_one_case_ii hlam_case_ii ht_nn
  have hD_le :
      (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 :=
    anisotropicHeisenbergParametricPath_snd_nonpos_case_ii hD_case_ii ht_nn
  rcases lt_or_eq_of_le hlam_ge with hlam_gt | hlam_eq
  · rcases lt_or_eq_of_le hD_le with hD_lt | hD_eq
    · obtain ⟨c, hc_strict⟩ :=
        exists_parityBlock_dressed_diag_strict_upper_bound
          (Λ := Λ) (N := N) A J
          ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
          ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) p
      exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
        (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
        (by simp)
        (by
          simp
          linarith)
        (by simpa using hlam_gt)
        (D := ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ))
        (by simp)
        (by simpa using hD_lt)
        (p := p) hc_strict
        (fun σ' σ _hne =>
          parityReachableSOnBlock_total_bipartiteCompleteGraph
            (Λ := Λ) (N := N) A hA_ne hB_ne hN_one σ' σ)
    · obtain ⟨c, hc_strict⟩ :=
        exists_parityBlock_dressed_diag_strict_upper_bound
          (Λ := Λ) (N := N) A J
          ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ) 0 p
      change axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2 p
      rw [hD_eq]
      exact
        axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_D_zero
          (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
          (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
          (by simp)
          (by
            simp
            linarith)
          (by simpa using hlam_gt)
          (p := p) hc_strict
          (fun σ' σ _hne =>
            bondParityReachableSOnBlock_total_bipartiteCompleteGraph
              (Λ := Λ) (N := N) A hA_ne hB_ne hN_one σ' σ)
  · rcases lt_or_eq_of_le hD_le with hD_lt | hD_eq
    · obtain ⟨c, hc_strict⟩ :=
        exists_parityBlock_dressed_diag_strict_upper_bound
          (Λ := Λ) (N := N) A J 1
          ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) p
      change axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2 p
      rw [← hlam_eq]
      exact
        axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_lambda_one
          (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
          (D := ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ))
          (by simp)
          (by simpa using hD_lt)
          (p := p) hc_strict
          (fun σ' σ _hne =>
            ionParityReachableSOnBlock_total_bipartiteCompleteGraph
              (Λ := Λ) (N := N) A hA_ne hB_ne hN σ' σ)
    · exact False.elim (hnot_corner ⟨hlam_eq.symm, hD_eq⟩)

/-- Non-corner case-(ii) parity-block full-min bound from total reachability.

This converts the non-corner PF/min callback into the block eigenspace bound at
the full anisotropic ground energy. -/
theorem axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot_corner :
      ¬ ((anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0))
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hp : p = 0 ∨ p = 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D t).1
          (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1 := by
  rcases axisSwappedParityBlockPFMinAt_of_total_reachability_noncorner
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hA_ne hB_ne hN
      hlam_case_ii hD_case_ii t ht hnot_corner p with
    ⟨ν, hν_bound, hν_eq_min⟩
  exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min
    (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star
    (lam := (anisotropicHeisenbergParametricPath lam D t).1)
    (D := (anisotropicHeisenbergParametricPath lam D t).2)
    p hp ν hν_bound hν_eq_min

/-- Path-global case-(ii) full `finrank <= 2` from total reachability away from
the SU(2) corner, plus a direct full corner bound. -/
theorem caseII_path_global_finrank_bound_of_total_reachability_and_corner
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (hcorner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            (anisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
            ((hermitianMinEigenvalue
              (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
                (anisotropicHeisenbergParametricPath lam D t).1
                (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 := by
  intro t ht
  by_cases hcorner_params :
      (anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0
  · exact hcorner t ht hcorner_params.1 hcorner_params.2
  · have h_even :=
      axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star
        hA_ne hB_ne hN hlam_case_ii hD_case_ii t ht hcorner_params
        0 (Or.inl rfl)
    have h_odd :=
      axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star
        hA_ne hB_ne hN hlam_case_ii hD_case_ii t ht hcorner_params
        1 (Or.inr rfl)
    exact anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one_general
      (Λ := Λ) (N := N) (J := J) hJself
      ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ)
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D t).1
          (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)
      h_even h_odd

/-- Path-global case-(ii) full `finrank <= 2` from total reachability and a
single SU(2)-corner full ground-state uniqueness bound at `(lambda,D) = (1,0)`.
-/
theorem caseII_path_global_finrank_bound_of_total_reachability_and_su2_unique
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_SU2_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 :=
  caseII_path_global_finrank_bound_of_total_reachability_and_corner
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star hA_ne hB_ne hN
    hlam_case_ii hD_case_ii
    (fun t _ht hlam hD => by
      rw [hlam, hD]
      exact le_trans h_SU2_unique (by omega))

end LatticeSystem.Quantum
