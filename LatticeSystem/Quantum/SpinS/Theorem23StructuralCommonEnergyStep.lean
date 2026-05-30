import LatticeSystem.Quantum.SpinS.Theorem23StructuralSectorLiftCasimir
import LatticeSystem.Quantum.SpinS.Theorem23StructuralMagSectorPF
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancyCasimir

/-!
# Structural adjacent-sector common-energy step (no `h_intermediate`)

(PR #3893): structural variant of `tasaki23_common_energy_step_legacy` (TIER 4 step) using
- `tasaki23_sector_lift_and_casimir_structural` (Step 1)
- `exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`
  (Thm23-#3887.9)
- `tasaki23_pf_sector_energy_eq_of_casimir` (already h_intermediate-free)

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural adjacent-sector common-energy step (no `h_intermediate`)**. -/
theorem tasaki23_common_energy_step
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {M : ℕ} (hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hM_lt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    {μ : ℝ} {vM : magConfigS V N M → ℝ}
    (hvM_pos : ∀ σ, 0 < vM σ)
    (hReEig_M : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * vM σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * vM σ)) :
    ∃ vM1 : magConfigS V N (M + 1) → ℝ, (∀ σ, 0 < vM1 σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N (M + 1)).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM1 σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * vM1 σ) := by
  have hM1_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right A N hM_mem hM_lt
  obtain ⟨hH_M, hCas_M⟩ := tasaki23_sector_lift_and_casimir_structural
    (N := N) (M := M) A c c_toy horient hsB hM_mem
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
    hA_ne hB_ne hN hvM_pos hReEig_M
  obtain ⟨μ', vM1, _hμ'_lt, hvM1_pos, hReEig_M1⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (N := N) (M := M + 1) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  obtain ⟨hH_M1, hCas_M1⟩ := tasaki23_sector_lift_and_casimir_structural
    (N := N) (M := M + 1) A c c_toy horient hsB hM1_mem
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
    hA_ne hB_ne hN hvM1_pos hReEig_M1
  have hMlt_left :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1 := by
    rw [tasaki23GroundStateSectors_mem_iff] at hM_mem
    omega
  have heq : μ = μ' :=
    tasaki23_pf_sector_energy_eq_of_casimir A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hM_mem hM1_mem hM_lt hMlt_left hvM_pos hvM1_pos hH_M hH_M1 hReEig_M hReEig_M1
      hCas_M hCas_M1
  exact ⟨vM1, hvM1_pos, by rw [heq]; exact hReEig_M1⟩

end LatticeSystem.Quantum
