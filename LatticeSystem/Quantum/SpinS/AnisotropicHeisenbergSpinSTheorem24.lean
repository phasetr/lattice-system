import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIITotalReachabilityTarget
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSDNonnegBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSLambdaOneBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSSU2Boundary

/-!
# General spin-S Tasaki Theorem 2.4 region wrapper

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file packages the existing general spin-`S`, `2 <= N`, target endpoints
for the Mattis--Nishimori anisotropic antiferromagnet.  It performs only the
final parameter-region dispatch: the case-(i) `D >= 0` endpoint handles
`-1 < lambda < 1`, the explicit SU(2) endpoint handles `(lambda,D)=(1,0)`,
the `lambda = 1`, `D > 0` endpoint handles the positive single-ion boundary,
and the case-(ii) total-reachability endpoint handles `lambda >= 1`, `D <= 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **General spin-`S`, `2 <= N`, Tasaki Theorem 2.4 target uniqueness wrapper**:
the target ground eigenspace has `finrank <= 1` throughout the parameter
region covered by the already proved case-(i), SU(2)-boundary, and case-(ii)
endpoints.  The hypotheses are the shared endpoint input surface: bipartite
coupling data, diagonal-shift bounds, balanced-sector bookkeeping, total
reachability for the case-(ii) bridge, and the MLM/Casimir/Theorem 2.3 SU(2)
endpoint data. -/
theorem anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hN_one : 1 ≤ N := by omega
  rcases h_region with h_case_i | h_boundary_or_case_ii
  · rcases h_case_i with ⟨hlam_lb, hlam_ub, hD_nonneg⟩
    exact anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym
      hc_axis_strict hA_ne hB_ne hN_one c_mlm c_toy hT23 hc_heis_strict
      hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero
      hlam_lb hlam_ub hD_nonneg
  rcases h_boundary_or_case_ii with h_lambda_one | h_case_ii
  · rcases h_lambda_one with ⟨hlam_eq, hD_nonneg⟩
    subst lam
    rcases lt_or_eq_of_le hD_nonneg with hD_pos | hD_zero
    · exact aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_pos_gen
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym
        hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23 hc_heis_strict
        hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero hD_pos
    · rw [← hD_zero]
      exact aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
        hN_one c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
  · rcases h_case_ii with ⟨hlam_case_ii, hD_case_ii⟩
    exact aHeisS_case_ii_target_finrank_le_one_of_totReach_MLM_casLadder_t23_pf
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym
      hA_ne hB_ne hN M_balanced h_balanced h_centered_nonzero
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      hlam_case_ii hD_case_ii

/-- **General spin-`S`, `2 <= N`, Tasaki Theorem 2.4 zero-magnetization
wrapper**: every non-zero target ground state has zero total `S^3`
magnetization throughout the packaged parameter region. -/
theorem aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0))
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  have huniq :=
    anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym
      hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23 hc_heis_strict
      hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero h_region
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
