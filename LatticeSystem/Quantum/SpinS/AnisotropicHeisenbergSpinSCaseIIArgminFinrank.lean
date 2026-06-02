import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIArgminFirstCrossing
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedMinEqFullAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingContradictionConditional
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingEqualityAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapAllMFromArgmin

/-!
# General spin-S case-(ii) argmin first-crossing contradiction from a finrank bound

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4103 isolated the remaining case-(ii) input as a contradiction at the
argmin first crossing.  This file proves that callback from the standard
first-crossing data plus a `finrank <= 2` bound at the selected crossing point.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Argmin first-crossing contradiction from a first-crossing `finrank <= 2` bound -/

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) argmin first-crossing contradiction from a
first-crossing `finrank <= 2` bound**.

The proof is the algebraic core of the first-crossing argument.  The argmin
property gives the balanced-sector ground-state equality at the selected first
crossing.  The selected crossing equality then supplies two embedded sector
ground eigenvectors at the same full ground energy; the assumed `finrank <= 2`
bound contradicts the balanced/non-balanced magnetization split. -/
theorem caseIIArgminFirstCrossingContradiction_of_first_crossing_finrank_bound
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
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
    (h_finrank_at_first_crossing :
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
                  Icc (0 : ℝ) 1))).2) : ℝ) : ℂ)) ≤ 2) :
    caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D := by
  classical
  intro M hM_nonempty hM_range hM_ne_balanced hne h_argmin t_first ht_first_def _hmem
  haveI := hM_nonempty
  have hM_centered_ne :
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0 :=
    h_centered_nonzero M hM_range hM_ne_balanced
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M lam D 0 :=
    h_strict_gap_at_SU2 M hM_nonempty hM_ne_balanced
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star N M_balanced M lam D hne h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star N M_balanced M lam D hne h_argmin)
  have h_eq_at_t := anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    hJ_star N M_balanced M lam D hne h_strict_chosen
  have h_bal_eq_full_def := balanced_min_eq_full_at_sInf
    hJ_star N M_balanced M lam D hne h_GS_at_SU2 h_below
  have h_bal_eq_full : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star
          (anisotropicHeisenbergParametricPath lam D t_first).1
          (anisotropicHeisenbergParametricPath lam D t_first).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D t_first).1
          (anisotropicHeisenbergParametricPath lam D t_first).2) := by
    rw [ht_first_def]
    exact h_bal_eq_full_def
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam D t_first).1
      (anisotropicHeisenbergParametricPath lam D t_first).2 N M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam D t_first).1
      (anisotropicHeisenbergParametricPath lam D t_first).2 N M
  have h_eq_at_t' : hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ_star
        (anisotropicHeisenbergParametricPath lam D t_first).1
        (anisotropicHeisenbergParametricPath lam D t_first).2) =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ_star
        (anisotropicHeisenbergParametricPath lam D t_first).1
        (anisotropicHeisenbergParametricPath lam D t_first).2) := by
    rw [ht_first_def]
    exact h_eq_at_t
  rw [h_eq_at_t'] at hΦ_M_eig
  rw [h_bal_eq_full] at hΦ_bal_eig
  have h_finrank_def := h_finrank_at_first_crossing M hM_nonempty hM_ne_balanced hne
  have h_finrank : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t_first).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t_first).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t_first).1
              (anisotropicHeisenbergParametricPath lam D t_first).2) : ℝ) : ℂ)) ≤ 2 := by
    rw [ht_first_def]
    exact h_finrank_def
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam D t_first).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam D t_first).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig hΦ_M_ne hM_centered_ne hΦ_M_eig

/-! ## Case-(ii) target wrappers from first-crossing `finrank <= 2` bounds -/

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from
first-crossing `finrank <= 2` bounds**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_first_crossing_finrank_bound
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
    (h_finrank_at_first_crossing :
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
                  Icc (0 : ℝ) 1))).2) : ℝ) : ℂ)) ≤ 2) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_argmin_first_crossing
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (caseIIArgminFirstCrossingContradiction_of_first_crossing_finrank_bound
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_balanced
      hlam_case_ii hD_case_ii h_centered_nonzero h_strict_gap_at_SU2
      h_GS_at_SU2 h_finrank_at_first_crossing)

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) target ground states have zero total
magnetization from first-crossing `finrank <= 2` bounds**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_first_crossing_finrank_bound
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
    (h_finrank_at_first_crossing :
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
                  Icc (0 : ℝ) 1))).2) : ℝ) : ℂ)) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_argmin_first_crossing
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (caseIIArgminFirstCrossingContradiction_of_first_crossing_finrank_bound
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_balanced
      hlam_case_ii hD_case_ii h_centered_nonzero h_strict_gap_at_SU2
      h_GS_at_SU2 h_finrank_at_first_crossing)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
