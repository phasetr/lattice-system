import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimir
import LatticeSystem.Quantum.SpinS.Theorem23PredictedEnergySectorAll
import LatticeSystem.Quantum.SpinS.Theorem23PFToyJointCasimir
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy

/-!
# The toy ground state has the predicted total Casimir in every admissible sector

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) —
generalising `tasaki23_toy_groundState_casimir_eq_predicted` (#3711, extremal sector) to
**every** admissible sector.

In sector `M`, the Marshall-positive Perron–Frobenius ground state of the bipartite toy
Hamiltonian is a joint Casimir eigenvector (#3657); its energy `μ ≤ E` (the predicted
minimum) via the predicted-energy witness at `M` (#3710-generalised, #3729) and the
ground-energy bound (#3680); so by the minimal-energy joint-eigenvector lemma (#3728) its
total Casimir is exactly `tasaki23PredictedCasimirValue A N`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The toy ground state has the predicted total Casimir in every admissible sector**
(for `|¬A| ≤ |A|`, non-degenerate `s_B > 0`): in each
`M ∈ tasaki23GroundStateSectors A N` there is a Marshall-positive `v > 0` whose embedding
`magSectorEmbedding (sign · v)` is a `(Ŝ_tot)²`-eigenvector at
`tasaki23PredictedCasimirValue A N`. -/
@[deprecated "Superseded by the h_intermediate-free canonical variant (Phase E refactor #3921); retained for backwards compatibility" (since := "2026-05-30")]

theorem tasaki23_toy_groundState_casimir_eq_predicted_at_legacy
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ v : magConfigS V N M → ℝ, (∀ σ, 0 < v σ) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  classical
  -- The Perron–Frobenius ground state of the bipartite toy Hamiltonian on sector M.
  obtain ⟨μ, v, _hμ_lt_c, hv_pos, hReEig⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_legacy
      (M := M) A N c (bipartiteCoupling_im A)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict h_intermediate
  set E := tasaki23PredictedCasimirValue (V := V) A N -
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
      ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)
    with hE
  -- Predicted-energy sector eigenvector φ at M (#3729) ⟹ μ ≤ E (#3680).
  obtain ⟨φ, hφ_ne, hφ⟩ := exists_predictedEnergy_sector_eigenvector_of_mem A horient hM
  have hw_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hv_pos σ
  have hμ_le : μ ≤ E :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict
      hw_marshall_pos hReEig hφ_ne hφ
  -- Lift the real sector eigen-equation to the full Hilbert space.
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    (J := bipartiteCoupling A) N (bipartiteCoupling_im A) hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding (bipartiteCoupling A)
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  -- The toy ground state is a joint Casimir eigenvector (#3657).
  obtain ⟨⟨γ_tot, htot⟩, ⟨γ_A, hA⟩, ⟨γ_B, hB⟩⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector_legacy A N c hc_strict h_intermediate hv_pos hH
  set w : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hw
  -- Energy: μ = γ_tot − γ_A − γ_B, so (γ_tot − γ_A − γ_B).re ≤ E.
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A htot hA hB
  have hμ_eq : γ_tot - γ_A - γ_B = (μ : ℂ) :=
    smul_left_injective ℂ (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
      (hEnergy.symm.trans hH)
  have henergy : (γ_tot - γ_A - γ_B).re ≤ E := by rw [hμ_eq, Complex.ofReal_re]; exact hμ_le
  -- Magnetization-level membership for #3728 (`k = |V|·N − M`).
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
  -- Predicted total Casimir (#3728).
  have hγ_tot : γ_tot = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) :=
    toy_joint_eigenvector_totalCasimir_eq_predicted A (Fintype.card V * N - M) horient hsB
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos) hw_mem htot hA hB
      (by
        have hthis := henergy
        rw [hE, tasaki23PredictedCasimirValue_eq_sub A horient] at hthis
        exact hthis)
  exact ⟨v, hv_pos, by rw [← hw, ← hγ_tot]; exact htot⟩

end LatticeSystem.Quantum
