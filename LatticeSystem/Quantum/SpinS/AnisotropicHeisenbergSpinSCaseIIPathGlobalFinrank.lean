import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIArgminFinrank

/-!
# General spin-S case-(ii) target bridge from path-global finrank bounds

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4104 reduced the case-(ii) argmin first-crossing contradiction to a
`finrank <= 2` bound at the selected first crossing.  This file repackages
that selected-point input as a path-global hypothesis: every point of the
deformation path on `[0, 1]` has full ground eigenspace `finrank <= 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## First-crossing finrank from path-global finrank -/

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) first-crossing finrank input from a path-global
finrank bound**.

If the full ground eigenspace of `Ĥ(γ(t))` has `finrank <= 2` for every
`t ∈ [0, 1]`, then the selected `sInf (perMCrossingSet M ∩ [0,1])` point used
by the argmin first-crossing bridge satisfies the exact finrank hypothesis
required by `caseIIArgminFirstCrossingContradiction_of_first_crossing_finrank_bound`. -/
theorem caseII_first_crossing_finrank_bound_of_path_global_finrank_bound
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ) {lam D : ℝ}
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_path_global_finrank :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2) :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
          Icc (0 : ℝ) 1).Nonempty →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D
              (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                Icc (0 : ℝ) 1))).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D
              (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                Icc (0 : ℝ) 1))).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D
                (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                  Icc (0 : ℝ) 1))).1
              (anisotropicHeisenbergParametricPath lam D
                (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                  Icc (0 : ℝ) 1))).2) : ℝ) : ℂ)) ≤ 2 := by
  intro M _hM_nonempty _hM_ne_balanced hne
  exact h_path_global_finrank
    (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1))
    (sInf_perMCrossingSet_inter_Icc_mem hJ_star N M_balanced M lam D hne).2

/-! ## Case-(ii) target wrappers from path-global finrank -/

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from a
path-global `finrank <= 2` bound**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_global_finrank_bound
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
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M lam D 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2))
    (h_path_global_finrank :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_first_crossing_finrank_bound
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2
    (caseII_first_crossing_finrank_bound_of_path_global_finrank_bound
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_path_global_finrank)

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) target ground states have zero total
magnetization from a path-global `finrank <= 2` bound**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_path_global_finrank_bound
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
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M lam D 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2))
    (h_path_global_finrank :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_first_crossing_finrank_bound
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2
    (caseII_first_crossing_finrank_bound_of_path_global_finrank_bound
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_path_global_finrank)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
