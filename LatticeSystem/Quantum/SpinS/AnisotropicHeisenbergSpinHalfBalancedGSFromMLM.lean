import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2FromMLM

/-!
# Spin-1/2 balanced ground sector from the Theorem 2.3 strict gap

Issue #3739 — Tasaki §2.5 Theorem 2.4.

This file packages the PR #4028 strict-gap theorem into the consumer form used
by the remaining Theorem 2.4 endpoint: every non-balanced non-empty sector lies
strictly above the balanced sector at the target point, hence the balanced
sector attains the full ground energy at that target point.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Spin-1/2 strict gap for all non-balanced sectors from Theorem 2.3 PF**:
the PR #4028 strict-gap theorem, repackaged with an arbitrary non-empty sector
`M` instead of a fixed `M_orig`. -/
theorem spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (M : ℕ) [Nonempty (magConfigS Λ 1 M)] (hM_ne : M ≠ M_balanced) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M lam' D' 1 := by
  classical
  have hM_range : M ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
    rw [Finset.mem_range]
    obtain ⟨σ⟩ := (inferInstance : Nonempty (magConfigS Λ 1 M))
    have hbound := magSumS_le σ.val
    rw [σ.property] at hbound
    exact Nat.lt_succ_of_le hbound
  exact spinHalf_anisotropicHeisenbergS_obligation_2_strict_gap_of_MLM_casimir_ladder_t23_pf
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
    c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
    M_balanced M h_balanced hM_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD'

set_option linter.style.longLine false in
/-- **Spin-1/2 balanced sector is the target ground sector from Theorem 2.3 PF**:
the balanced sector minimum at `(lambda', D')` equals the full anisotropic
Hamiltonian ground energy. -/
theorem spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D') :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') := by
  classical
  have h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M) hJ_star lam' D') := by
    intro M hM_nonempty hM_ne
    haveI := hM_nonempty
    have hpath :=
      spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf
        A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
        c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
        M_balanced h_balanced h_centered_nonzero
        hlam'_lb hlam'_ub hD' M hM_ne
    unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
    simpa using hpath
  exact hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    hJ_star 1 M_balanced lam' D' h_strict_gap

end LatticeSystem.Quantum
