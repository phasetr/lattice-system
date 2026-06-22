import LatticeSystem.Quantum.SpinS.Problem25dBalancedPFEndpointCore
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM

/-!
# Tasaki Problem 2.5.d: balanced Perron--Frobenius endpoint

This module connects the balanced-sector Perron--Frobenius vector from the
Theorem 2.3 / Theorem 2.4 SU(2) endpoint to the sector-supported
Problem 2.5.d signed-correlation positivity wrapper.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, solution pp. 498--499, equations
(S.22)--(S.23), and the surrounding Marshall--Lieb--Mattis Theorem 2.3
infrastructure on pp. 41--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Balanced PF endpoint -/

set_option linter.style.longLine false in
/-- Problem 2.5.d balanced Perron--Frobenius endpoint: the balanced Theorem 2.3
PF vector, rewritten in the sector-supported Marshall form, has strictly
positive signed two-spin correlation for every cross-sublattice pair. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_tasaki23_balanced_pf_cross
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      ∃ v0 : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) → ℝ,
        (∀ σ, 0 < v0 σ) ∧
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (v0 σ : ℂ))) ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun σ :
                magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
              marshallSignS A σ.1 * (v0 σ : ℂ))) =
          (μ : ℂ) •
            (magSectorEmbedding (fun σ :
                magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
              marshallSignS A σ.1 * (v0 σ : ℂ))) ∧
        finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ)) ≤ 1 ∧
        0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
          twoSpinCorrelationS x y
            (magSectorEmbedding (fun σ :
                magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
              marshallSignS A σ.1 * (v0 σ : ℂ)))).re := by
  classical
  set M0 := (Finset.univ.filter (fun z : V => A z = true)).card * N with hM0def
  obtain ⟨μ, hmin_eq, _hsectors_singleton, huniq⟩ :=
    exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder_t23_pf
      (V := V) A N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
  obtain ⟨μ0, hmin_eq0, hsector, _hglobal⟩ :=
    exists_tasaki23_common_energy_eq_hermitianMinEigenvalue A N c hT23
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      hN hcardA hcardB
  have hμ0_eq : μ0 = μ := by
    rw [hmin_eq] at hmin_eq0
    exact hmin_eq0.symm
  subst μ0
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
    rw [hM0def, tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq]
  haveI : Nonempty (magConfigS V N M0) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v0, _hμ_lt, hv0_pos, hΦreal_eig, _huniq0⟩ := hsector M0 hM0_mem
  set Φreal : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N M0 =>
      (((marshallSignS A τ.1).re * v0 τ : ℝ) : ℂ))
    with hΦreal_def
  set Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N M0 =>
      marshallSignS A τ.1 * (v0 τ : ℂ))
    with hΦ_def
  have hΦreal_eq : Φreal = Φ := by
    ext σ
    by_cases hσ : magSumS σ = M0
    · rw [hΦreal_def, hΦ_def, magSectorEmbedding_apply_of_mem _ hσ,
        magSectorEmbedding_apply_of_mem _ hσ, marshallSignS_eq_ofReal_re,
        ← Complex.ofReal_mul]
      simp
    · rw [hΦreal_def, hΦ_def, magSectorEmbedding_apply_of_not_mem _ hσ,
        magSectorEmbedding_apply_of_not_mem _ hσ]
  have hΦreal_ne : Φreal ≠ 0 := by
    intro hzero
    let τ : magConfigS V N M0 := Classical.arbitrary _
    have hτ_zero := congrFun hzero τ.1
    rw [hΦreal_def, magSectorEmbedding_apply_subtype] at hτ_zero
    have hreal_zero : (marshallSignS A τ.1).re * v0 τ = 0 := by
      exact_mod_cast congrArg Complex.re hτ_zero
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv0_zero : v0 τ = 0 := by
      calc
        v0 τ = ((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) * v0 τ := by
          rw [hsq, one_mul]
        _ = (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v0 τ) := by ring
        _ = 0 := by rw [hreal_zero, mul_zero]
    exact (ne_of_gt (hv0_pos τ)) hv0_zero
  have hΦ_ne : Φ ≠ 0 := by
    rwa [hΦreal_eq] at hΦreal_ne
  have hΦeig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
    rw [← hΦreal_eq]
    simpa [hmin_eq] using hΦreal_eig
  obtain ⟨cswap, hswap, hcswap⟩ :=
    exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute_of_ne_zero
      (H := heisenbergHamiltonianS J N)
      (U := (axisSwapUnitarySSpinS N).tensorInv V)
      (μ := (μ : ℂ)) huniq hΦ_ne hΦeig
      (heisenbergHamiltonianS_commute_axisSwapUnitarySSpinS_tensorInv
        (V := V) (N := N) J).eq
      (axisSwapUnitarySSpinS_tensorInv_conjTranspose_mul_self (V := V) (N := N))
  obtain ⟨crot, hrot, hcrot⟩ :=
    exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute_of_ne_zero
      (H := heisenbergHamiltonianS J N)
      (U := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
      (μ := (μ : ℂ)) huniq hΦ_ne hΦeig
      (heisenbergHamiltonianS_commute_manyBodySpinSRot3 (N := N) J (Real.pi / 2)).eq
      (manyBodySpinSRot3_conjTranspose_mul_self (V := V) (N := N) (Real.pi / 2))
  have hpos :
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinCorrelationS x y Φ).re := by
    rw [hΦ_def]
    exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_axis_phases
      A hxy hAxy v0 hv0_pos
      (by
        rw [hM0def]
        exact exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne_balanced_sector
          A hxy hAxy hN)
      cswap crot hswap hcswap hrot hcrot
  refine ⟨μ, hmin_eq, v0, hv0_pos, ?_, ?_, huniq, ?_⟩
  · simpa [Φ, hΦ_def, hM0def] using hΦ_ne
  · simpa [Φ, hΦ_def, hM0def] using hΦeig
  · simpa [Φ, hΦ_def, hM0def] using hpos

end LatticeSystem.Quantum
