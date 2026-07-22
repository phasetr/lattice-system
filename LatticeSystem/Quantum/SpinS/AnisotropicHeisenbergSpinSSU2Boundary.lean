import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSMLMEndpoint

/-!
# General spin-S Theorem 2.4 SU(2) boundary endpoint

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file exposes the explicit general spin-`S` target endpoint at the SU(2)
point `(lambda, D) = (1, 0)`.  The proof is the direct Heisenberg-to-anisotropic
transport already used by the strict and boundary deformation wrappers, but
without any deformation path or parity-block irreducibility input.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- General spin-`S` target uniqueness at the SU(2) point `(lambda, D) = (1, 0)`
from the Theorem 2.3 MLM/Casimir/Perron-Frobenius endpoint. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_lambda_one_D_zero_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
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
  exact anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
    (Λ := Λ) (N := N) hJ_star hμ_min huniq_heis

set_option linter.style.longLine false in
/-- General spin-`S` zero total `S^3` magnetization at the SU(2) point
`(lambda, D) = (1, 0)` from the Theorem 2.3 MLM/Casimir/Perron-Frobenius
endpoint. -/
theorem anisotropicHeisenbergS_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf_lambda_one_D_zero_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J 1 0 N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_lambda_one_D_zero_general
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J 1 0
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
