import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIPathCrossingFromSet
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSInfMem

/-!
# General spin-S case-(ii) crossing-set contradiction from first crossing

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4101 reduced the remaining case-(ii) target contradiction to a contradiction
for non-empty `perMCrossingSet M ∩ Icc 0 1`.  This file shifts that input to the
first-crossing point: if the `sInf` point of every non-empty crossing set is
contradictory, then the crossing set itself cannot be non-empty.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Crossing-set non-emptiness contradiction from first crossing -/

/-- **General spin-S case-(ii) crossing-set contradiction from a first-crossing
contradiction**.

If the first crossing point `sInf (perMCrossingSet M ∩ Icc 0 1)` is
contradictory whenever the crossing set is non-empty, then non-emptiness of the
crossing set is itself contradictory. -/
theorem anisotropicHeisenbergS_case_ii_crossing_set_contradiction_of_first_crossing
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ}
    (h_first_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t_first : ℝ,
          t_first =
              sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                Icc (0 : ℝ) 1) →
          t_first ∈
              perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1 →
          False)
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1).Nonempty →
      False := by
  intro hne
  exact h_first_crossing_contradiction M inferInstance hM_ne
    (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1))
    rfl
    (sInf_perMCrossingSet_inter_Icc_mem hJ_star N M_balanced M lam D hne)

/-! ## Case-(ii) target wrappers from first crossing -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from a
first-crossing contradiction**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_first_crossing
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
    (h_first_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t_first : ℝ,
          t_first =
              sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                Icc (0 : ℝ) 1) →
          t_first ∈
              perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1 →
          False) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_set_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_set_contradiction_of_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        h_first_crossing_contradiction M hM_ne)

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from a first-crossing contradiction**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_first_crossing
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
    (h_first_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t_first : ℝ,
          t_first =
              sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩
                Icc (0 : ℝ) 1) →
          t_first ∈
              perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1 →
          False)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_set_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_set_contradiction_of_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        h_first_crossing_contradiction M hM_ne)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
