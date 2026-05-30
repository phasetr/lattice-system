import LatticeSystem.Quantum.SpinS.Theorem23ToyWitness
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound
import LatticeSystem.Quantum.SpinS.JointPredictedSectorEigenvector

/-!
# The toy-Hamiltonian ground state is a predicted-total-Casimir witness

Issue #3658 (the SINGLE remaining obligation of the sound Tasaki §2.5 Theorem 2.3
route, #3542): construct a Marshall-positive sector state whose embedding is a
total-Casimir eigenvector at the predicted value `tasaki23PredictedCasimirValue A N`.

Assembly (for `|¬A| ≤ |A|`, so the extremal sector is `M = min(|A|,|¬A|)·N = |¬A|·N`):

* The Perron–Frobenius ground state of the bipartite toy Hamiltonian on the sector
  `M` exists and is Marshall positive
  (`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_legacy`),
  giving `v > 0` with `Ĥ_re (sign·v) = μ (sign·v)`.
* The predicted-energy sector eigenvector `φ` (#3710) sits at
  `E = predicted − s_A(s_A+1) − s_B(s_B+1)`; by Marshall positivity of the PF ground
  state (`tasaki23_toy_sector_groundEnergy_le_of_witness`, #3680) the ground-state
  energy satisfies `μ ≤ E`.
* Lifting `Ĥ_re (sign·v) = μ (sign·v)` to the full Hilbert space and feeding `μ ≤ E`
  into the witness capstone (`tasaki23_toy_groundState_casimir_eq_predicted_of_energy_le`,
  #3656) pins the total Casimir of the embedded PF ground state to the predicted value.

This is exactly the `hw_cas` witness consumed by the overlap pin
`tasaki23_pf_groundState_casimir_eq_predicted_of_witness_legacy` (#3656's downstream), which
transfers the predicted total Casimir to the actual antiferromagnetic ground state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42 (eq. 2.5.12).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The toy-Hamiltonian ground state is a predicted-total-Casimir witness** (for
`|¬A| ≤ |A|`): in the extremal sector `M = min(|A|,|¬A|)·N` there is a Marshall-positive
`v > 0` whose embedding `magSectorEmbedding (sign · v)` is a `(Ŝ_tot)²`-eigenvector at
the predicted value `tasaki23PredictedCasimirValue A N`.  This discharges the single
remaining obligation of the sound Perron–Frobenius route (Issue #3658). -/
theorem tasaki23_toy_groundState_casimir_eq_predicted
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    [Nonempty (magConfigS V N
      (min (Finset.univ.filter (fun x : V => A x = true)).card
        (Finset.univ.filter (fun x : V => (! A x) = true)).card * N))]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ v : magConfigS V N
        (min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N) → ℝ,
      (∀ σ, 0 < v σ) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  classical
  set M := min (Finset.univ.filter (fun x : V => A x = true)).card
      (Finset.univ.filter (fun x : V => (! A x) = true)).card * N with hM
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
  -- The predicted-energy sector eigenvector φ at M (= |¬A|·N for |¬A| ≤ |A|).
  have hMeq : M = (Finset.univ.filter (fun x : V => (! A x) = true)).card * N := by
    rw [hM, min_eq_right horient]
  set E := tasaki23PredictedCasimirValue (V := V) A N -
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
      ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
        (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)
    with hE
  obtain ⟨φ, hφ_ne, hφ⟩ :
      ∃ φ : magConfigS V N M → ℝ, φ ≠ 0 ∧
        (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ =
          E • φ := by
    rw [hMeq]
    exact exists_predictedEnergy_sector_eigenvector A horient
  -- Marshall positivity of the PF ground state witness `sign · v`.
  have hw_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hv_pos σ
  -- Ground-state energy bound μ ≤ E (#3680).
  have hμ_le : μ ≤ E :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict
      hw_marshall_pos hReEig hφ_ne hφ
  -- Lift the real sector eigen-equation to the full Hilbert space.
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    (J := bipartiteCoupling A) N (bipartiteCoupling_im A) hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding (bipartiteCoupling A)
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  -- Witness capstone (#3656): predicted total Casimir.
  have hCas := tasaki23_toy_groundState_casimir_eq_predicted_of_energy_le
    A N c hc_strict h_intermediate hv_pos hH hμ_le
  exact ⟨v, hv_pos, hCas⟩

end LatticeSystem.Quantum
