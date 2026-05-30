import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimirAt
import LatticeSystem.Quantum.SpinS.Theorem23StructuralMagSectorPF
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFJointCasimir

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Structural toy ground state has predicted total Casimir (no `h_intermediate`)

(Thm23-#3887.10): structural variant of
`tasaki23_toy_groundState_casimir_eq_predicted_at_legacy` using
- `exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector` (Thm23-#3887.9)
- `tasaki23_toy_groundState_joint_casimir_eigenvector` (Thm23-#3887.5)

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural toy GS has predicted total Casimir at admissible sector (no `h_intermediate`)**. -/
theorem tasaki23_toy_groundState_casimir_eq_predicted_at
    (A : V → Bool) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ v : magConfigS V N M → ℝ, (∀ σ, 0 < v σ) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  classical
  obtain ⟨μ, v, _hμ_lt_c, hv_pos, hReEig⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (N := N) (M := M) A c (bipartiteCoupling_im A)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict hA_ne hB_ne hN
  set E := tasaki23PredictedCasimirValue (V := V) A N -
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
      ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)
    with hE
  obtain ⟨φ, hφ_ne, hφ⟩ := exists_predictedEnergy_sector_eigenvector_of_mem A horient hM
  have hw_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hv_pos σ
  have hμ_le : μ ≤ E :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict
      hw_marshall_pos hReEig hφ_ne hφ
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    (J := bipartiteCoupling A) N (bipartiteCoupling_im A) hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding (bipartiteCoupling A)
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  obtain ⟨⟨γ_tot, htot⟩, ⟨γ_A, hA⟩, ⟨γ_B, hB⟩⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector A c hc_strict
      hA_ne hB_ne hN hv_pos hH
  set w : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hw
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A htot hA hB
  have hμ_eq : γ_tot - γ_A - γ_B = (μ : ℂ) :=
    smul_left_injective ℂ (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
      (hEnergy.symm.trans hH)
  have henergy : (γ_tot - γ_A - γ_B).re ≤ E := by rw [hμ_eq, Complex.ofReal_re]; exact hμ_le
  have hM_le : M ≤ Fintype.card V * N := by
    rw [tasaki23GroundStateSectors_mem_iff] at hM
    have hmax : max (Finset.univ.filter (fun x : V => A x = true)).card
        (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤ Fintype.card V := by
      rw [← tasaki23_card_filter_A_add_card_notA A]
      exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    calc M ≤ _ := hM.2
      _ ≤ Fintype.card V * N := Nat.mul_le_mul_right N hmax
  have hw_mem : w ∈ magSubspaceS V N
      (((Fintype.card V * N - M : ℕ) : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)) := by
    have h := magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := M)
      (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    rw [hw]
    convert h using 2
    rw [Nat.cast_sub hM_le]
    push_cast
    ring
  have hγ_tot : γ_tot = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) :=
    toy_joint_eigenvector_totalCasimir_eq_predicted A (Fintype.card V * N - M) horient hsB
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos) hw_mem htot hA hB
      (by
        have hthis := henergy
        rw [hE, tasaki23PredictedCasimirValue_eq_sub A horient] at hthis
        exact hthis)
  exact ⟨v, hv_pos, by rw [← hw, ← hγ_tot]; exact htot⟩

end LatticeSystem.Quantum
