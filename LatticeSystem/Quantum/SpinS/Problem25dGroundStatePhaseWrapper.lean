import LatticeSystem.Quantum.SpinS.Problem25dLongitudinalComponentEquality
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM

/-!
# Tasaki Problem 2.5.d: ground-state phase wrapper

This module removes the explicit axis-swap and z-axis rotation phase
hypotheses from the Problem 2.5.d signed correlation wrapper.  A normalized
non-zero Marshall-positive Heisenberg eigenvector in a one-dimensional
eigenspace supplies both unit-modulus phases by the ground-state phase bridges
already used in Problem 2.5.c.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution pp. 498--499, equations
(S.22)--(S.23); the SU(2) phase input follows the context around
Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenspace phase wrapper -/

/-- Problem 2.5.d ground-state phase wrapper: a normalized non-zero
Marshall-positive Heisenberg eigenvector in a one-dimensional eigenspace
supplies the axis-swap and z-axis rotation phases required by the PR #4074
signed dot-product positivity wrapper. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_eigenphase
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (J : V → V → ℂ) (μ : ℂ)
    (c : (V → Fin (N + 1)) → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne : (fun σ => marshallSignS A σ * (c σ : ℂ)) ≠ 0)
    (hΦnorm :
      dotProduct (star (fun σ => marshallSignS A σ * (c σ : ℂ)))
        (fun σ => marshallSignS A σ * (c σ : ℂ)) = 1)
    (hΦeig :
      (heisenbergHamiltonianS J N).mulVec
          (fun σ => marshallSignS A σ * (c σ : ℂ)) =
        μ • (fun σ => marshallSignS A σ * (c σ : ℂ))) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  obtain ⟨cswap, hswap, hcswap⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_axisSwapUnitarySSpinS_tensorInv
      (V := V) (N := N) J μ huniq hΦ_ne hΦnorm hΦeig
  obtain ⟨crot, hrot, hcrot⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_manyBodySpinSRot3
      (V := V) (N := N) J μ (Real.pi / 2) huniq hΦ_ne hΦnorm hΦeig
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_axis_phases
    A hxy hAxy hN c hc_pos cswap crot hswap hcswap hrot hcrot

/-! ## Balanced MLM ground-state wrapper -/

set_option linter.style.longLine false in
/-- Problem 2.5.d balanced MLM ground-state wrapper: the balanced
Marshall--Lieb--Mattis/SU(2) endpoint supplies one-dimensionality of the
Heisenberg ground eigenspace, so a normalized non-zero Marshall-positive
ground eigenvector satisfies the signed cross-sublattice two-spin correlation
positivity conclusion. -/
theorem twoSpinCorrelationS_signed_re_pos_of_tasaki23_balanced_MLM_groundState
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
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (coeff : (V → Fin (N + 1)) → ℝ) (hcoeff_pos : ∀ σ, 0 < coeff σ)
    (hΦ_ne : (fun σ => marshallSignS A σ * (coeff σ : ℂ)) ≠ 0)
    (hΦnorm :
      dotProduct (star (fun σ => marshallSignS A σ * (coeff σ : ℂ)))
        (fun σ => marshallSignS A σ * (coeff σ : ℂ)) = 1)
    (hΦ :
      (heisenbergHamiltonianS J N).mulVec
          (fun σ => marshallSignS A σ * (coeff σ : ℂ)) =
        (hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
          (Λ := V) hJ_real' N) : ℂ) •
          (fun σ => marshallSignS A σ * (coeff σ : ℂ))) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (fun σ => marshallSignS A σ * (coeff σ : ℂ))).re := by
  obtain ⟨μ, hmin_eq, _hsectors_singleton, huniq⟩ :=
    exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder_t23_pf
      (V := V) A N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
  have hΦμ :
      (heisenbergHamiltonianS J N).mulVec
          (fun σ => marshallSignS A σ * (coeff σ : ℂ)) =
        (μ : ℂ) • (fun σ => marshallSignS A σ * (coeff σ : ℂ)) := by
    simpa [hmin_eq] using hΦ
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_eigenphase
    (V := V) A hxy hAxy hN J (μ : ℂ) coeff hcoeff_pos huniq hΦ_ne hΦnorm hΦμ

end LatticeSystem.Quantum
