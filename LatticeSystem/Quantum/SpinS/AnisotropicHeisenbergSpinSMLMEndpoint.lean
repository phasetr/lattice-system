import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSObligation2FromSU2Unique
import LatticeSystem.Quantum.SpinS.Theorem24SU2BaseCase
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM

/-!
# General spin-S Theorem 2.4 target endpoint from the MLM/Casimir SU(2) endpoint

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file composes the general spin-`S` Marshall--Lieb--Mattis/Casimir
SU(2)-endpoint uniqueness theorem with the general spin-`S` deformation
wrappers.  The result removes the abstract SU(2)-global-uniqueness input from
the target uniqueness and zero-magnetization endpoints in strict case (i).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Transport a Heisenberg SU(2)-minimum eigenspace `finrank <= 1` bound to the
anisotropic Hamiltonian at `(lambda, D) = (1, 0)`, using the SU(2)-point
reduction `anisotropicHeisenbergS J 1 0 N = heisenbergHamiltonianS J N`. -/
theorem anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (N + 1))]
    {μ : ℝ}
    (hμ :
      hermitianMinEigenvalue
        (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ N) = μ)
    (huniq :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) (μ : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) :
          ℝ) : ℂ)) ≤ 1 := by
  have hmin :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) = μ := by
    simpa [anisotropicHeisenbergS_one_zero] using hμ
  have h_eigsp_eq :=
    anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
      (Λ := Λ) (N := N) J
      (((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) :
          ℝ) : ℂ))
  rw [h_eigsp_eq]
  rw [hmin]
  exact huniq

/-- **General spin-S target uniqueness from the MLM/Casimir SU(2) endpoint**:
Theorem 2.3 supplies the SU(2)-point Heisenberg ground-eigenspace uniqueness,
which is transported to the anisotropic SU(2) point and then fed to the
general spin-`S` deformation wrapper. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
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
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ)) ≤ 1 := by
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
    exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder_t23_pf
      (V := Λ) A N c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq hN hcardA hcardB
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
      (Λ := Λ) (N := N) hJ_star hμ_min huniq_heis
  exact anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_general
    A hJim hJnn hJpos hJself hJbip hJ_sym hc_axis_strict hA_ne hB_ne hN hJ_star
    M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
    hlam'_lb hlam'_ub hD'

/-- **General spin-S target zero-magnetization from the MLM/Casimir SU(2)
endpoint**: the target uniqueness theorem above feeds the existing
uniqueness-implies-zero-magnetization theorem. -/
theorem anisotropicHeisenbergS_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
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
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
