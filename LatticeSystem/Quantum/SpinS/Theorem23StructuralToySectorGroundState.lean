import LatticeSystem.Quantum.SpinS.Theorem23StructuralSectorExistence
import LatticeSystem.Quantum.SpinS.Theorem23StructuralToySectorLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23PredictedEnergySectorAll
import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimir
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Structural toy sector ground state at predicted energy (no `h_intermediate`)

(Thm23-#3887.19): structural variant of the per-sector toy ground-state
at predicted-energy package (the original `toy_sector_groundState_at_predicted`
witness was removed together with `Theorem23ToyFinal.lean` in PR #3917). Uses
- `tasaki_2_5_theorem_2_3_sector_existence` (Thm23-#3887.16)
- `tasaki23_toy_sector_energy_ge_predicted` (Thm23-#3887.17)
- `tasaki23_toy_sector_groundEnergy_le_of_witness` (already h_intermediate-free)
- `exists_predictedEnergy_sector_eigenvector_of_mem` (already h_intermediate-free)

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural per-sector toy ground state at the predicted minimum energy
(no `h_intermediate`)**. -/
theorem toy_sector_groundState_at_predicted
    (A : V → Bool) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)] :
    ∃ vM : magConfigS V N M → ℝ,
      (bipartiteToyMinEnergyPredicted (Λ := V) A N).re < c ∧ (∀ σ, 0 < vM σ) ∧
      (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ))) =
        ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM σ) =
        (bipartiteToyMinEnergyPredicted (Λ := V) A N).re •
          (fun σ => (marshallSignS A σ.1).re * vM σ) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = (bipartiteToyMinEnergyPredicted (Λ := V) A N).re ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * vM τ)) := by
  classical
  set E := (bipartiteToyMinEnergyPredicted (Λ := V) A N).re with hEdef
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hH_M, _hsupp, huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence (M := M) A c (bipartiteCoupling_im A)
      (fun x y => by
        rw [Complex.star_def, Complex.conj_eq_iff_im]; exact bipartiteCoupling_im A x y)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict hA_ne hB_ne hN
  have hReEig_M : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec
      (fun σ => (marshallSignS A σ.1).re * vM σ) =
      μM • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
    have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      (bipartiteCoupling A) (M := M) hH_M
    rw [magSectorRestriction_magSectorEmbedding] at hc
    have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
      (bipartiteCoupling_im A) hc
    simpa only [Complex.ofReal_re] using hre
  have hwM_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM_pos σ
  have hge : E ≤ μM :=
    tasaki23_toy_sector_energy_ge_predicted (N := N) A c horient hc_strict
      hA_ne hB_ne hN
      (φ := fun σ => (marshallSignS A σ.1).re * vM σ)
      (by
        intro hzero
        have h0 := congrFun hzero (Classical.arbitrary (magConfigS V N M))
        have hp := hwM_marshall_pos (Classical.arbitrary (magConfigS V N M))
        simp only [Pi.zero_apply] at h0
        rw [h0, mul_zero] at hp
        exact lt_irrefl 0 hp)
      hReEig_M
  obtain ⟨φ, hφ_ne, hφ⟩ := exists_predictedEnergy_sector_eigenvector_of_mem A horient hM
  have hval :
      tasaki23PredictedCasimirValue (V := V) A N -
          ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1) =
        E := by
    rw [hEdef]
    have hcplx : bipartiteToyMinEnergyPredicted (Λ := V) A N =
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
              ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) *
            ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
                ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) +
              1) -
            ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
              (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 +
                1) : ℝ) := by
      unfold bipartiteToyMinEnergyPredicted
      push_cast
      ring
    rw [hcplx, Complex.ofReal_re, tasaki23PredictedCasimirValue_eq_sub A horient]
  have hφ_E : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ =
      E • φ := by rw [← hval]; exact hφ
  have hle : μM ≤ E :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict hwM_marshall_pos hReEig_M
      hφ_ne hφ_E
  have hμM_eq : μM = E := le_antisymm hle hge
  subst hμM_eq
  exact ⟨vM, hμM_lt, hvM_pos, hH_M, hReEig_M, huniq⟩

end LatticeSystem.Quantum
