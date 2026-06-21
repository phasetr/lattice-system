import LatticeSystem.Quantum.SpinS.ConnectedSectorIrreducible
import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23PFConstancyCasimir
import LatticeSystem.Quantum.SpinS.ConnectedTheorem23Core

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Tasaki §2.5 Theorem 2.3 for a general CONNECTED bipartite coupling

(Issue #4609, PR3): extends the complete-bipartite
`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`
(`Theorem23StructuralGeneralFinal.lean`) to a general *connected* bipartite
coupling `J`, positive only on the edges of a connected bipartite graph `G` and
vanishing off `G`.

## Strategy

The dressed matrix `shiftedDressedSReMatrixOnMagSector A J N c M` depends only on
`J` (not on a graph).  The strict-positivity hypothesis `hJ_pos` of the
complete-bipartite chain flows down *only* through Perron–Frobenius
irreducibility `isIrreducible_shiftedDressedSReMatrixOnMagSector`.  We therefore
parameterise the whole PF-consuming chain by the *irreducibility result*

    `hIrred : ∀ (M) [Nonempty (magConfigS V N M)],
       (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible`

as a hypothesis (the `_of_irreducible` variants below), making each chain lemma
graph-agnostic.  For the connected case we feed
`isIrreducible_shiftedDressedSReMatrixOnMagSector_connected` (PR3 Step 1);
the complete case still feeds `isIrreducible_shiftedDressedSReMatrixOnMagSector`.

The remaining ingredients of the assembly — `tasaki23_general_hOutside`,
`tasaki23_eigenvalue_ge_common`, `tasaki23_pf_sector_energy_eq_of_casimir`, and
the entire toy-coupling Casimir branch — use only `hJ_nn` (non-negativity), which
a connected `J` satisfies, so they are reused unchanged.

## Output

`tasaki_2_5_theorem_2_3_data_of_connected` proves the *data* conclusion of
`tasaki_2_5_theorem_2_3` (the `∃ μ, (per-sector ground states) ∧ (global min)`
body) directly from the connected hypotheses, dropping the complete-bipartite
`hJ_pos` premise (which a connected `J` cannot satisfy).  This is the usable
input for discharging the §4.1 Theorem 4.4 axiom.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobeniusMain

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
/-! ## Common-energy chain parameterised by irreducibility -/

/-- **Adjacent-sector common-energy step from supplied irreducibility witnesses**.
Graph-agnostic variant of `tasaki23_common_energy_step`.  Two irreducibility
witnesses are threaded: one for sector `M`, one for sector `M + 1`. -/
theorem tasaki23_common_energy_step_of_irreducible
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
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
    (hIrred_M : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible)
    (hIrred_M1 : (shiftedDressedSReMatrixOnMagSector A J N c (M + 1)).IsIrreducible)
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
  obtain ⟨hH_M, hCas_M⟩ := tasaki23_sector_lift_and_casimir_of_irreducible
    (N := N) (M := M) A c c_toy horient hsB hM_mem hJ_real hc_strict_toy
    hA_ne hB_ne hN hIrred_M hvM_pos hReEig_M
  obtain ⟨μ', vM1, _hμ'_lt, hvM1_pos, hReEig_M1⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
      (N := N) (M := M + 1) A c hJ_real hIrred_M1
  obtain ⟨hH_M1, hCas_M1⟩ := tasaki23_sector_lift_and_casimir_of_irreducible
    (N := N) (M := M + 1) A c c_toy horient hsB hM1_mem hJ_real hc_strict_toy
    hA_ne hB_ne hN hIrred_M1 hvM1_pos hReEig_M1
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

/-- **Common ground-state energy across all admissible sectors, from a supplied
family of irreducibility witnesses**. Graph-agnostic variant of
`tasaki23_common_groundEnergy`: `hIrred` provides irreducibility uniformly at
every nonempty magnetization sector. -/
theorem tasaki23_common_groundEnergy_of_irreducible
    (A : V → Bool) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (hIrred : ∀ (M : ℕ) [Nonempty (magConfigS V N M)],
      (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible) :
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
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_of_irreducible
      (N := N) (M := min cardA cardB * N) A c hJ_real (hIrred (min cardA cardB * N))
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
      exact tasaki23_common_energy_step_of_irreducible (N := N) A c c_toy horient hsB hJ_real
        hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
        hA_ne hB_ne hN hM_mem hM_lt (hIrred M) (hIrred (M + 1)) hvM_pos hReEig_M
  intro M hM
  rw [tasaki23GroundStateSectors_mem_iff] at hM
  exact hstep M hM.1 hM.2

/-! ## Connected assembly -/

omit [DecidableEq V] in
/-- A non-empty domain underlies any non-zero real sector vector. -/
private theorem nonempty_magConfigS_of_fn_ne_zero_connected {M : ℕ}
    {φ : magConfigS V N M → ℝ} (hne : φ ≠ 0) : Nonempty (magConfigS V N M) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hne (funext (fun τ => (h.false τ).elim))

/-- **Tasaki §2.5 Theorem 2.3 data form for a general CONNECTED bipartite coupling.**

Proves the `∃ μ, (per-sector Marshall-positive ground states with uniqueness) ∧
(global energy minimality)` conclusion of `tasaki_2_5_theorem_2_3` directly from
the hypotheses of a *connected* bipartite antiferromagnetic coupling: `J` is real,
symmetric, non-negative, vanishes within a sublattice, vanishes off the connected
bipartite graph `G`, and is strictly positive on the edges of `G`.

This drops the complete-bipartite `hJ_pos` premise (which a connected `J` with
edges removed cannot satisfy) and is the usable input for discharging the §4.1
Theorem 4.4 axiom, whose hypotheses are exactly those of a connected-graph
coupling.

The proof mirrors `tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`, but
builds the sector irreducibility from
`isIrreducible_shiftedDressedSReMatrixOnMagSector_connected` (PR3 Step 1) and
feeds it to the `_of_irreducible` chain. -/
theorem tasaki_2_5_theorem_2_3_data_of_connected
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
        [Nonempty (magConfigS V N M)] →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ σ, 0 < v σ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
            (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
            (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
            (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
            μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
              ∀ τ : magConfigS V N M,
                (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') := by
  classical
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    refine ⟨b, ?_⟩
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b
    · rfl
    · rw [hAb] at hbf; cases hbf
  have hIrred : ∀ (M : ℕ) [Nonempty (magConfigS V N M)],
      (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
    intro M _
    exact isIrreducible_shiftedDressedSReMatrixOnMagSector_connected
      (N := N) (M := M) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc_strict
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_groundEnergy_of_irreducible (N := N) A c c_toy horient hsB
      hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hIrred
  refine ⟨μ, ?_, ?_⟩
  · intro M hM _hNe
    obtain ⟨μM, vM, hμM_lt, hvM_pos, hH_M, _hsupp, huniq⟩ :=
      tasaki_2_5_theorem_2_3_sector_existence_of_irreducible (N := N) (M := M) A c
        hJ_real hJ_real' (hIrred M)
    have hReEig_M : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * vM σ) =
        μM • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
      have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        J (M := M) hH_M
      rw [magSectorRestriction_magSectorEmbedding] at hc
      have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
        hJ_real hc
      simpa only [Complex.ofReal_re] using hre
    have hvM_marshall_pos : ∀ σ,
        0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM σ) := fun σ => by
      rw [← mul_assoc, marshallSignS_re_sq, one_mul]; exact hvM_pos σ
    have hmarvM_ne : (fun σ => (marshallSignS A σ.1).re * vM σ) ≠ 0 := by
      intro h
      have h0 := congrFun h (Classical.arbitrary (magConfigS V N M))
      have hp := hvM_marshall_pos (Classical.arbitrary (magConfigS V N M))
      simp only [Pi.zero_apply] at h0
      rw [h0, mul_zero] at hp
      exact lt_irrefl 0 hp
    obtain ⟨wM, hwM_pos, hReEig_wM⟩ := hcommon M hM
    have hwM_marshall_pos : ∀ σ,
        0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * wM σ) := fun σ => by
      rw [← mul_assoc, marshallSignS_re_sq, one_mul]; exact hwM_pos σ
    have hle₁ : μ ≤ μM :=
      heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
        hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig_wM hwM_marshall_pos
        hmarvM_ne hReEig_M
    have hle₂ : μM ≤ μ :=
      heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
        hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig_M hvM_marshall_pos
        (by
          intro h
          have h0 := congrFun h (Classical.arbitrary (magConfigS V N M))
          have hp := hwM_marshall_pos (Classical.arbitrary (magConfigS V N M))
          simp only [Pi.zero_apply] at h0
          rw [h0, mul_zero] at hp
          exact lt_irrefl 0 hp)
        hReEig_wM
    have hμM_eq : μM = μ := le_antisymm hle₂ hle₁
    refine ⟨vM, ?_, hvM_pos, ?_, ?_⟩
    · rw [← hμM_eq]; exact hμM_lt
    · rw [← hμM_eq]; exact hH_M
    · intro μ' Ψ' h1 h2 h3
      obtain ⟨he, hr⟩ := huniq h1 h2 h3
      exact ⟨he.trans hμM_eq, hr⟩
  · refine tasaki23_eigenvalue_ge_common A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon (fun {M} hM_non {μM φ} hφ_ne hφ => ?_)
    haveI : Nonempty (magConfigS V N M) := nonempty_magConfigS_of_fn_ne_zero_connected hφ_ne
    exact tasaki23_general_hOutside A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hcommon hM_non hφ_ne hφ

end LatticeSystem.Quantum
