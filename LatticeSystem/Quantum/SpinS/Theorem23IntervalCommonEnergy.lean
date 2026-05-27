import LatticeSystem.Quantum.SpinS.Theorem23PFSectorCasimir
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancyCasimir
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall

/-!
# Common ground-state energy across every admissible sector (Casimir route)

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) — TIER 4.

For a connected bipartite antiferromagnetic coupling `J` the Marshall-positive
Perron–Frobenius ground state of the dressed sector matrix exists in every magnetisation
sector (`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`).  In
every *admissible* sector `M ∈ tasaki23GroundStateSectors A N` that ground state carries
the predicted total Casimir (#3731), and the adjacent-sector Casimir constancy (#3713)
then forces equal energies between neighbouring admissible sectors.  Iterating along the
interval `[min·N, max·N]` produces a single common ground-state energy `μ` realised by a
Marshall-positive ground state in *every* admissible sector.

This is the constancy half of Tasaki's §2.5 Theorem 2.3 argument; it consumes only the
predicted total Casimir (discharged globally by #3731), **never** the lowered-Marshall
`site_sum` positivity of the earlier `Theorem23CommonEnergyPredecessor` route.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Per-sector ground-state lift to the full Hilbert space plus predicted Casimir.**
Given the Marshall-positive real sector eigen-equation `hReEig` of a connected bipartite
antiferromagnetic coupling `J` in an admissible sector `M`, the embedded vector is a
full-space `H`-eigenvector at the same energy and a `(Ŝ_tot)²`-eigenvector at
`tasaki23PredictedCasimirValue A N`. -/
theorem tasaki23_sector_lift_and_casimir
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hReEig : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ)) :
    ((heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
    ((totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal (J := J) N hJ_real
    hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding J
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  refine ⟨hH, ?_⟩
  exact tasaki23_pf_groundState_casimir_eq_predicted_sector A N c c_toy horient hsB hM
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy h_intermediate hv_pos hH

/-- **Adjacent-sector common-energy step (Casimir route).** If the Marshall-positive
Perron–Frobenius ground state in admissible sector `M` has energy `μ`, and `M` is not the
right endpoint of the admissible interval, then the Marshall-positive ground state in the
next sector `M + 1` also has energy `μ`. -/
theorem tasaki23_common_energy_step
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
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
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
  -- Full-space lift and predicted Casimir for sector M.
  obtain ⟨hH_M, hCas_M⟩ := tasaki23_sector_lift_and_casimir A N c c_toy horient hsB hM_mem
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy h_intermediate hvM_pos
    hReEig_M
  -- Marshall-positive ground state in sector M + 1, with its full-space lift and Casimir.
  obtain ⟨μ', vM1, _hμ'_lt, hvM1_pos, hReEig_M1⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M + 1) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
  obtain ⟨hH_M1, hCas_M1⟩ := tasaki23_sector_lift_and_casimir A N c c_toy horient hsB hM1_mem
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy h_intermediate hvM1_pos
    hReEig_M1
  -- Casimir constancy forces equal energies.
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

/-- **Common ground-state energy across all admissible sectors (Tasaki §2.5, constancy).**
There is a single energy `μ` such that in *every* admissible sector
`M ∈ tasaki23GroundStateSectors A N` the connected bipartite antiferromagnetic coupling `J`
has a Marshall-positive Perron–Frobenius ground state of energy `μ`. -/
theorem tasaki23_common_groundEnergy
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
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
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ μ : ℝ, ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
  classical
  set cardA := (Finset.univ.filter (fun x : V => A x = true)).card with hcardA
  set cardB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcardB
  -- `max·N ≤ card V · N`, so every admissible sector is nonempty.
  have hmax_le : max cardA cardB * N ≤ Fintype.card V * N := by
    apply Nat.mul_le_mul_right
    rw [hcardA, hcardB, ← tasaki23_card_filter_A_add_card_notA A]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  -- Marshall-positive ground state in the base (left-endpoint) sector `min·N`.
  haveI hbaseNe : Nonempty (magConfigS V N (min cardA cardB * N)) :=
    magConfigS_nonempty_of_le_card_mul
      (le_trans (Nat.mul_le_mul_right N (min_le_max)) hmax_le)
  obtain ⟨μ, v₀, _hμ_lt, hv₀_pos, hReEig₀⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := min cardA cardB * N) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, ?_⟩
  -- Inductive predicate `Q M`: the sector-`M` Marshall-positive ground state has energy `μ`.
  have hstep : ∀ M, min cardA cardB * N ≤ M → M ≤ max cardA cardB * N →
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
    intro M hMge
    induction M, hMge using Nat.le_induction with
    | base =>
      intro _
      exact ⟨v₀, hv₀_pos, hReEig₀⟩
    | succ M hMge IH =>
      intro hM1_le
      have hM_le : M ≤ max cardA cardB * N := Nat.le_of_succ_le hM1_le
      have hM_lt : M < max cardA cardB * N := hM1_le
      obtain ⟨vM, hvM_pos, hReEig_M⟩ := IH hM_le
      have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
        rw [tasaki23GroundStateSectors_mem_iff]; exact ⟨hMge, hM_le⟩
      haveI : Nonempty (magConfigS V N M) :=
        magConfigS_nonempty_of_le_card_mul (le_trans hM_le hmax_le)
      haveI : Nonempty (magConfigS V N (M + 1)) :=
        magConfigS_nonempty_of_le_card_mul (le_trans hM1_le hmax_le)
      exact tasaki23_common_energy_step A N c c_toy horient hsB hJ_real hJ_real' hJ_pos hJ_nn
        hJ_sym hJ_bipartite hc_strict hc_strict_toy h_intermediate hM_mem hM_lt hvM_pos hReEig_M
  intro M hM
  rw [tasaki23GroundStateSectors_mem_iff] at hM
  exact hstep M hM.1 hM.2

end LatticeSystem.Quantum
