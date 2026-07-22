import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2SU2UniqueOnly
import LatticeSystem.Quantum.SpinS.Theorem24SU2BaseCase
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM

/-!
# Spin-1/2 Theorem 2.4 obligation (2) from the MLM/Casimir SU(2) endpoint

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

This file composes the PR #4025 MLM/Casimir endpoint with the spin-half
deformation capstone.  The resulting theorem removes the abstract
full-SU(2)-point uniqueness input from the spin-half obligation boundary:
the `finrank <= 1` hypothesis is constructed from Theorem 2.3, the balanced
cardinality condition, the balanced-sector PF simplicity input, and the
Casimir/ladder obstruction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Transport a Heisenberg SU(2)-minimum eigenspace `finrank <= 1` bound to the
anisotropic Hamiltonian at `(lambda, D) = (1, 0)`, using the SU(2)-point
reduction `anisotropicHeisenbergS J 1 0 N = heisenbergHamiltonianS J N`. -/
private theorem anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (1 + 1))]
    {μ : ℝ}
    (hμ : hermitianMinEigenvalue
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ 1) = μ)
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := Λ) J 1)) (μ : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ 1 1 0) :
          ℝ) : ℂ)) ≤ 1 := by
  have hmin :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ 1 1 0) = μ := by
    simpa [anisotropicHeisenbergS_one_zero] using hμ
  have h_eigsp_eq := anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
    (Λ := Λ) (N := 1) J
    (((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ 1 1 0) : ℝ) : ℂ))
  rw [h_eigsp_eq]
  rw [hmin]
  exact huniq

/-- **Spin-1/2 obligation (2) from the MLM/Casimir SU(2) endpoint**: the
deformation contradiction follows from the Theorem 2.3 common-energy endpoint
and the balanced zero-Casimir ladder obstruction, without an abstract
full-SU(2)-point uniqueness hypothesis. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder
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
    (h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := Λ) hJ_star 1) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J 1
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * 1))) (μ : ℂ)) ≤ 1)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1) :
    False := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    LatticeSystem.Quantum.exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder
      (V := Λ) A 1 c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq (by norm_num) hcardA hcardB h_sector_pf
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg
      (Λ := Λ) hJ_star hμ_min huniq_heis
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only
    A hJim hJnn hJpos hJself hJbip hc_axis_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique

/-- **Spin-1/2 obligation (2) from the MLM/Casimir endpoint with sector PF
constructed from Theorem 2.3**: this is the same deformation contradiction as
`spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder`, but the
balanced-sector Perron--Frobenius simplicity callback is obtained internally
from the structural Theorem 2.3 Marshall-positive sector witness. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1) :
    False := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  have h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := Λ) hJ_star 1) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J 1
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * 1))) (μ : ℂ)) ≤ 1 :=
    fun μ hmin_eq =>
      tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
        (V := Λ) A 1 c_mlm hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
        hJpos hc_heis_strict h_card_eq (by norm_num) hcardA hcardB hmin_eq
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
    c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq h_sector_pf
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig

/-- **Spin-1/2 obligation (2) strict gap from the MLM/Casimir endpoint with
Theorem 2.3 sector PF**: at the target point of the deformation path, every
non-balanced sector has strictly larger minimum energy than the balanced
sector.  This is the strict-gap statement obtained by negating the violation
consumed by
`spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_strict_gap_of_MLM_casimir_ladder_t23_pf
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D') :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_orig lam' D' 1 := by
  classical
  exact lt_of_not_ge (by
    intro h_violation_orig
    exact spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
      hlam'_lb hlam'_ub hD' h_violation_orig)

end LatticeSystem.Quantum
