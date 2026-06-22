import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagneticCore


/-!
# Strict outside-sector energy separation (ferrimagnetic case)

Tasaki §4.1 Theorem 4.4, Issue #4617 step 2.  This file generalizes the BALANCED
strict obstruction
`tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction`
(`Theorem24SU2GlobalUniquenessFromMLM.lean`, the `|A| = |B|` case) to the GENERAL
ferrimagnetic case (`|A| ≠ |B|`), and provides a connected-coupling wrapper.

A magnetization sector
`M ∉ tasaki23GroundStateSectors A N = [min(cA, cB)·N, max(cA, cB)·N]`
(where `cA = |{A}|`, `cB = |{¬A}|`) has STRICTLY higher ground energy than the
admissible common energy `μ`.  This is the final gate for discharging the §4.1
Theorem 4.4 axiom.

## The Casimir equality-obstruction argument

Suppose an outside sector `M` had a non-zero `μ`-eigenvector `φ`.  By
`tasaki23_general_hOutside` it gives `μ ≤ μM`.  To kill the equality case
`μ = μM`:

1. Lift `φ` to a full Heisenberg `μ`-eigenvector `Φ` in centered weight
   `center − M` (`center = |V|·N/2`).
2. Ladder `Φ` inward to the admissible band edge (`min·N` by lowering, or `max·N`
   by raising), landing NON-ZERO at the same energy `μ`.
3. The band edge is one-dimensional (connected PF, `finrank ≤ 1`), and its PF
   ground vector `Φ0` is a `(Ŝ_tot)²`-eigenvector at the predicted Casimir value
   `tasaki23PredictedCasimirValue A N = S_tot(S_tot+1)`.  By `finrank ≤ 1` the
   landed vector is proportional to `Φ0`, so it too has Casimir `S_tot(S_tot+1)`.
4. `(Ŝ_tot)²` commutes with the ladder, so the predicted Casimir value is pulled
   BACK to `Φ`: `Φ` is a `(Ŝ_tot)²`-eigenvector at `S_tot(S_tot+1)`.
5. But `Φ ∈ magSubspaceS V N (center − M)` with `|center − M| > S_tot`, so the
   Casimir lower bound forces eigenvalue `≥ |center−M|·(|center−M|+1) >
   S_tot(S_tot+1)`.  Contradiction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §2.5 Theorem 2.3 (Marshall–Lieb–Mattis, p. 42) and §4.1 Theorem 4.4
(Shen–Qiu–Tian, chain (4.1.16), pp. 77–78).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Connected-coupling wrapper -/

/-- **Strict outside-sector ordering for a connected bipartite coupling**.
For a general connected bipartite antiferromagnetic coupling `J` (real, Hermitian,
symmetric, non-negative, sublattice-vanishing, strictly positive on the edges of a
connected bipartite graph `G`), every non-admissible magnetization sector `M`
has dressed sector ground energy `μM` STRICTLY above the admissible common energy
`μ`.

This assembles `tasaki23_strict_hOutside_ferrimagnetic` from the connected
Theorem 2.3 data (`tasaki_2_5_theorem_2_3_data_of_connected`), the connected
per-sector predicted Casimir
(`tasaki23_pf_groundState_casimir_eq_predicted_sector_of_irreducible`), and the
connected per-sector finrank `≤ 1`
(`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`).
It is the final gate for discharging the §4.1 Theorem 4.4 axiom. -/
theorem tasaki23_strict_hOutside_of_connected
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
        ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
              (fun σ => (marshallSignS A σ.1).re * vM σ) =
            μ • (fun σ => (marshallSignS A σ.1).re * vM σ)) ∧
      (∀ {M : ℕ}, M ∉ tasaki23GroundStateSectors (V := V) A N →
        [Nonempty (magConfigS V N M)] →
        ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
          μ < μM) := by
  classical
  set cardA := (Finset.univ.filter (fun x : V => A x = true)).card with hcardA_def
  set cardB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcardB_def
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  -- Connected per-sector irreducibility witnesses.
  have hIrred : ∀ (M : ℕ) [Nonempty (magConfigS V N M)],
      (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
    intro M _
    exact isIrreducible_shiftedDressedSReMatrixOnMagSector_connected
      (N := N) (M := M) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc_strict
  -- Connected common ground energy `μ` + per-admissible-sector real eigenvectors.
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_groundEnergy_of_irreducible (N := N) A c c_toy horient hsB
      hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy hA_ne hB_ne hN hIrred
  -- Both band edges are admissible and nonempty.
  have hsum : cardA + cardB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
  have hmax_le_card : max cardA cardB ≤ Fintype.card V := by
    rw [← hsum]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hmin_mem : min cardA cardB * N ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_left_mem A N
  have hmax_mem : max cardA cardB * N ∈ tasaki23GroundStateSectors (V := V) A N := by
    rw [tasaki23GroundStateSectors_mem_iff]
    exact ⟨Nat.mul_le_mul_right N min_le_max, le_refl _⟩
  haveI hminNe : Nonempty (magConfigS V N (min cardA cardB * N)) :=
    magConfigS_nonempty_of_le_card_mul
      (le_trans (Nat.mul_le_mul_right N min_le_max) (Nat.mul_le_mul_right N hmax_le_card))
  haveI hmaxNe : Nonempty (magConfigS V N (max cardA cardB * N)) :=
    magConfigS_nonempty_of_le_card_mul (Nat.mul_le_mul_right N hmax_le_card)
  -- Build the left-edge predicted-Casimir witness `Φ0_min`.
  obtain ⟨vmin, hvmin_pos, hReEig_min⟩ := hcommon (min cardA cardB * N) hmin_mem
  set Φ0_min : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun σ : magConfigS V N (min cardA cardB * N) =>
        (((marshallSignS A σ.1).re * vmin σ : ℝ) : ℂ)) with hΦ0min_def
  have hΦ0min_ne : Φ0_min ≠ 0 :=
    tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvmin_pos
  obtain ⟨hΦ0min_eig, hΦ0min_cas⟩ :=
    tasaki23_sector_lift_and_casimir_of_irreducible (N := N) (M := min cardA cardB * N)
      A c c_toy horient hsB hmin_mem hJ_real hc_strict_toy hA_ne hB_ne hN
      (hIrred (min cardA cardB * N)) hvmin_pos hReEig_min
  have hΦ0min_mem : Φ0_min ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
        ((min cardA cardB * N : ℕ) : ℂ)) := by
    rw [hΦ0min_def]
    exact magSectorEmbedding_mem_magSubspaceS _
  have h_pf_min : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (min cardA cardB * N)))
        (μ : ℂ)) ≤ 1 :=
    heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
      (N := N) (M := min cardA cardB * N) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym
      hJ_bipartite hc_strict hvmin_pos hReEig_min
  -- Build the right-edge predicted-Casimir witness `Φ0_max`.
  obtain ⟨vmax, hvmax_pos, hReEig_max⟩ := hcommon (max cardA cardB * N) hmax_mem
  set Φ0_max : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun σ : magConfigS V N (max cardA cardB * N) =>
        (((marshallSignS A σ.1).re * vmax σ : ℝ) : ℂ)) with hΦ0max_def
  have hΦ0max_ne : Φ0_max ≠ 0 :=
    tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvmax_pos
  obtain ⟨hΦ0max_eig, hΦ0max_cas⟩ :=
    tasaki23_sector_lift_and_casimir_of_irreducible (N := N) (M := max cardA cardB * N)
      A c c_toy horient hsB hmax_mem hJ_real hc_strict_toy hA_ne hB_ne hN
      (hIrred (max cardA cardB * N)) hvmax_pos hReEig_max
  have hΦ0max_mem : Φ0_max ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
        ((max cardA cardB * N : ℕ) : ℂ)) := by
    rw [hΦ0max_def]
    exact magSectorEmbedding_mem_magSubspaceS _
  have h_pf_max : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (max cardA cardB * N)))
        (μ : ℂ)) ≤ 1 :=
    heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
      (N := N) (M := max cardA cardB * N) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym
      hJ_bipartite hc_strict hvmax_pos hReEig_max
  refine ⟨μ, hcommon, ?_⟩
  intro M hM_non _ μM φ hφ_ne hφ
  exact tasaki23_strict_hOutside_ferrimagnetic A N c hJ_real hJ_real' hJ_nn hJ_sym
    hJ_bipartite hc_strict hcommon hΦ0min_ne hΦ0min_eig hΦ0min_mem hΦ0min_cas h_pf_min
    hΦ0max_ne hΦ0max_eig hΦ0max_mem hΦ0max_cas h_pf_max hM_non hφ_ne hφ

end LatticeSystem.Quantum
