import LatticeSystem.Quantum.SpinS.Theorem23StructuralCommonEnergyStep

/-!
# Structural common ground-state energy across all admissible sectors
(no `h_intermediate`)

(PR #3893): structural variant of `tasaki23_common_groundEnergy` (TIER 4 constancy)
using
- `exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_structural`
  (Thm23-#3887.9 from PR #3891)
- `tasaki23_common_energy_step_structural` (Step 2 of this PR)

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural common ground-state energy (no `h_intermediate`)**. -/
theorem tasaki23_common_groundEnergy_structural
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
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ μ : ℝ, ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
  classical
  set cardA := (Finset.univ.filter (fun x : V => A x = true)).card with hcardA
  set cardB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcardB
  have hmax_le : max cardA cardB * N ≤ Fintype.card V * N := by
    apply Nat.mul_le_mul_right
    rw [hcardA, hcardB, ← tasaki23_card_filter_A_add_card_notA A]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  haveI hbaseNe : Nonempty (magConfigS V N (min cardA cardB * N)) :=
    magConfigS_nonempty_of_le_card_mul
      (le_trans (Nat.mul_le_mul_right N (min_le_max)) hmax_le)
  obtain ⟨μ, v₀, _hμ_lt, hv₀_pos, hReEig₀⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_structural
      (N := N) (M := min cardA cardB * N) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  refine ⟨μ, ?_⟩
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
      exact tasaki23_common_energy_step_structural (N := N) A c c_toy horient hsB hJ_real
        hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
        hA_ne hB_ne hN hM_mem hM_lt hvM_pos hReEig_M
  intro M hM
  rw [tasaki23GroundStateSectors_mem_iff] at hM
  exact hstep M hM.1 hM.2

end LatticeSystem.Quantum
