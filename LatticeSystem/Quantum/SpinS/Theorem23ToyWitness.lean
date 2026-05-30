import LatticeSystem.Quantum.SpinS.Theorem23ToyCasimirPin
import LatticeSystem.Quantum.SpinS.Theorem23ToySublatticeBounds
import LatticeSystem.Quantum.SpinS.Theorem23ExtremalSector
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toy ground state is the predicted total-Casimir witness (modulo the energy bound)

Issue #3674 (Issue #3658 PR 4 / #3542): the capstone assembling PRs 1–4 into the
`#3656` witness form, leaving the reference energy bound as the single hypothesis.

In the extremal sector `M = min(|A|, |¬A|)·N`, the Marshall-positive toy ground
state — given only the **reference energy bound** `μ ≤ predicted − s_A(s_A+1) −
s_B(s_B+1)` — is a `(Ŝ_tot)²`-eigenvector at exactly the predicted Casimir value:

  `(Ŝ_tot)² Ψ = (tasaki23PredictedCasimirValue A N) · Ψ`.

This threads: the joint Casimir eigenvector (#3657), the sublattice Casimir
bounds (#3677), the toy energy formula (#3673, eigenvalue uniqueness against
`Ĥ_toy Ψ = μ Ψ`), the extremal-sector magnetization (#3678), the two-sided pin
(#3676), and the Hermitian realness of the eigenvalue.  It is exactly the witness
required by `tasaki23_pf_groundState_casimir_eq_predicted_of_witness` (#3656).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Toy ground state is the predicted-Casimir witness (modulo the energy bound)**:
in the extremal sector `M = min(|A|, |¬A|)·N`, the Marshall-positive toy ground
state with toy energy `μ ≤ predicted − s_A(s_A+1) − s_B(s_B+1)` is a `(Ŝ_tot)²`
eigenvector at the predicted Casimir value. -/
theorem tasaki23_toy_groundState_casimir_eq_predicted_of_energy_le
    (A : V → Bool) (N : ℕ) (c : ℝ)
    [Nonempty (magConfigS V N
      (min (Finset.univ.filter (fun x : V => A x = true)).card
        (Finset.univ.filter (fun x : V => (! A x) = true)).card * N))]
    (hc_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    {v : magConfigS V N
      (min (Finset.univ.filter (fun x : V => A x = true)).card
        (Finset.univ.filter (fun x : V => (! A x) = true)).card * N) → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hμ : μ ≤
      tasaki23PredictedCasimirValue (V := V) A N -
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  set Ψ := magSectorEmbedding
    (fun σ : magConfigS V N _ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hΨ
  have hΨ_ne : Ψ ≠ 0 := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos
  -- Joint Casimir eigenvector (#3657): total and sublattice eigen-equations.
  obtain ⟨⟨γ_tot, htot⟩, _, _⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector A N c hc_strict h_intermediate hv_pos hH
  -- Sublattice Casimir bounds (#3677).
  obtain ⟨⟨γ_A, hA_eq, hA_bd⟩, ⟨γ_B, hB_eq, hB_bd⟩⟩ :=
    tasaki23_toy_groundState_sublattice_casimir_re_le A N c hc_strict h_intermediate hv_pos hH
  -- Toy energy formula (#3673): Ĥ_toy Ψ = (γ_tot − γ_A − γ_B) • Ψ.
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A htot hA_eq hB_eq
  -- Ĥ_toy = heisenbergHamiltonianS (bipartiteCoupling A); so μ = γ_tot − γ_A − γ_B.
  have hμ_eq : (γ_tot - γ_A - γ_B) = (μ : ℂ) := by
    have hHtoy : heisenbergToyHamiltonianS (Λ := V) A N = heisenbergHamiltonianS (bipartiteCoupling A) N :=
      rfl
    rw [hHtoy] at hEnergy
    have hcombine : (γ_tot - γ_A - γ_B) • Ψ = (μ : ℂ) • Ψ := hEnergy.symm.trans hH
    have := sub_eq_zero.mpr hcombine
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hΨ_ne
  have hμ_re : (γ_tot - γ_A - γ_B).re ≤
      tasaki23PredictedCasimirValue (V := V) A N -
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1) := by
    rw [hμ_eq]; simpa using hμ
  -- Membership in the magnetization subspace + extremal-sector identification (#3678).
  have hmem := magSectorEmbedding_mem_magSubspaceS (V := V) (N := N)
    (fun σ : magConfigS V N _ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
  have hM := tasaki23_extremal_sector_magnetization_re_eq_predicted (V := V) A N
  -- Pin (#3676): γ_tot.re = predicted.
  have hγ_re : γ_tot.re = tasaki23PredictedCasimirValue (V := V) A N :=
    tasaki23_total_casimir_re_eq_predicted_of_bounds A hΨ_ne hmem hM htot hA_bd hB_bd hμ_re
  -- Realness: γ_tot.im = 0 (Hermitian eigenvalue).
  have hstar := isHermitian_eigenvalue_star_eq (totalSpinSSquared_isHermitian V N) htot hΨ_ne
  have hγ_im : γ_tot.im = 0 := by
    have := Complex.conj_eq_iff_im.mp hstar
    exact this
  have hγ_eq : γ_tot = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hγ_re, Complex.ofReal_re]
    · rw [hγ_im, Complex.ofReal_im]
  rw [← hγ_eq]; exact htot

end LatticeSystem.Quantum
