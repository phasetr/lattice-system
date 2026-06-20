import LatticeSystem.Quantum.SpinS.Theorem23StructuralBipartiteToy
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFSectorCasimir
import LatticeSystem.Quantum.SpinS.MagConfig

/-!
# Tasaki §4.1 (Theorem 4.4): the total-spin value at the centered sector

This file builds the *total-spin value* ingredient (PR3) of Tasaki's finite-volume proof of
Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order).  The chain (4.1.16) is evaluated on
the *centered* (`Ŝ_tot^{(3)} = 0`, centered magnetization `m = 0`) ground state `Φ⁰`, where the
unstaggered transverse expectation equals
`⟨Φ⁰, ((Ŝ_tot)² − (Ŝ_tot^{(3)})²) Φ⁰⟩ = S_tot(S_tot + 1) − 0 = S_tot(S_tot + 1)`,
with `S_tot = ||A| − |¬A|| · N / 2` (`tasaki23PredictedTotalSpin`) and predicted Casimir value
`S_tot(S_tot + 1)` (`tasaki23PredictedCasimirValue`).

The construction is *coupling-agnostic in the structural sense*: it takes the Theorem 2.3
per-sector Marshall-positive ground-state data as the hypothesis `tasaki_2_5_theorem_2_3 A N J c`,
so it applies to **any** coupling `J` once that coupling is shown to satisfy Theorem 2.3 (the
standard bipartite coupling via `tasaki_2_5_theorem_2_3_bipartiteToy`, or any future general-`J`
discharge).  The Casimir-value identification additionally needs the underlying `J`-positivity and
the comparison toy coupling `bipartiteCoupling A`, supplied as the same hypotheses
`tasaki_2_5_theorem_2_3` itself consumes, plus a toy diagonal bound `c_toy` — these are *families
of couplings*, not one fixed coupling.

The result feeds the capstone PR that discharges `shenQiuTian_ferrimagnetic_lro` in
`FerrimagneticLRO.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78; §2.5, Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The centered magnetization sector is admissible -/

omit [DecidableEq V] in
/-- **The centered magnetization sector lies in the Theorem 2.3 admissible interval.**

If the `magSumS` value `M0` is the center of the spectrum (centered magnetization `0`, i.e.
`|V| · N / 2 − M0 = 0` over `ℂ`), then `M0 ∈ tasaki23GroundStateSectors A N`, because
`2 · M0 = |V| · N = (|A| + |¬A|) · N` forces `min(|A|, |¬A|) · N ≤ M0 ≤ max(|A|, |¬A|) · N`. -/
theorem tasaki23GroundStateSectors_center_mem (A : V → Bool) (N M0 : ℕ)
    (hM0_center : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M0 : ℂ) = 0) :
    M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
  classical
  set cA := (Finset.univ.filter (fun x : V => A x = true)).card with hcA
  set cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcB
  -- Turn the centering equation over `ℂ` into the integer identity `2 * M0 = (cA + cB) * N`.
  have hM0_two : 2 * M0 = (cA + cB) * N := by
    have hcard : cA + cB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
    have h := sub_eq_zero.mp hM0_center
    have hcast : (Fintype.card V : ℂ) * (N : ℂ) = 2 * (M0 : ℂ) := by
      have h2 : (Fintype.card V : ℂ) * (N : ℂ) / 2 * 2 = (M0 : ℂ) * 2 := by
        rw [h]
      rw [div_mul_cancel₀] at h2
      · linear_combination h2
      · norm_num
    have hcast' : ((2 * M0 : ℕ) : ℂ) = (((cA + cB) * N : ℕ) : ℂ) := by
      push_cast [hcard]
      linear_combination -hcast
    exact_mod_cast hcast'
  rw [tasaki23GroundStateSectors_mem_iff]
  rw [← hcA, ← hcB]
  refine ⟨?_, ?_⟩
  · -- `min cA cB * N ≤ M0` from `2 * min cA cB ≤ cA + cB` and `2 * M0 = (cA + cB) * N`.
    have hmin : 2 * (min cA cB * N) ≤ 2 * M0 := by
      rw [hM0_two]
      calc 2 * (min cA cB * N) = (2 * min cA cB) * N := by ring
        _ ≤ (cA + cB) * N := by
              apply Nat.mul_le_mul_right
              have := min_le_left cA cB
              have := min_le_right cA cB
              omega
    omega
  · -- `M0 ≤ max cA cB * N` from `cA + cB ≤ 2 * max cA cB`.
    have hmax : 2 * M0 ≤ 2 * (max cA cB * N) := by
      rw [hM0_two]
      calc (cA + cB) * N ≤ (2 * max cA cB) * N := by
              apply Nat.mul_le_mul_right
              have := le_max_left cA cB
              have := le_max_right cA cB
              omega
        _ = 2 * (max cA cB * N) := by ring
    omega

/-! ## The centered ground state with the predicted total-spin Casimir value -/

/-- **The centered Marshall-positive Theorem 2.3 ground state with predicted total Casimir.**

Coupling-agnostic via the Theorem 2.3 ground-state data `hT23 : tasaki_2_5_theorem_2_3 A N J c`:
from the Theorem-2.3 per-sector Marshall-positive ground states (at the global minimum energy `μ`)
and the centering hypothesis `|V| · N / 2 − M0 = 0`, this produces a ground vector `Φ⁰` of the
spin-`S` Heisenberg Hamiltonian that is

* nonzero,
* an eigenvector of `heisenbergHamiltonianS J N` at the global-minimum eigenvalue `μ`,
* globally energy-minimal (`μ ≤ μ'` for every nonzero `H`-eigenvalue `μ'`),
* a centered `Ŝ_tot^{(3)}` eigenvector, `Ŝ_tot^{(3)} Φ⁰ = 0` (centered magnetization `0`), and
* a `Ŝ_tot²` eigenvector at the predicted Casimir value
  `tasaki23PredictedCasimirValue A N = S_tot(S_tot + 1)`.

The `J`-positivity hypotheses, the comparison toy coupling `bipartiteCoupling A`, and the toy
diagonal bound `c_toy` are exactly the data that the Theorem-2.3 Casimir identification
(`tasaki23_pf_groundState_casimir_eq_predicted_sector`) consumes; they describe *families* of
admissible couplings, not a single fixed coupling.  This is the (4.1.16) `S_tot`-value ingredient
of Theorem 4.4. -/
theorem exists_centered_groundState_predictedCasimir_of_tasaki23
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    {M0 : ℕ}
    (hM0_center : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M0 : ℂ) = 0) :
    ∃ (μ : ℝ) (Φ0 : (V → Fin (N + 1)) → ℂ),
      Φ0 ≠ 0 ∧
      (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0 ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ') ∧
      (totalSpinSOp3 V N).mulVec Φ0 = 0 ∧
      (totalSpinSSquared V N).mulVec Φ0 =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ0 := by
  classical
  -- The center is an admissible sector and is non-empty.
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_center_mem A N M0 hM0_center
  have hM0_le : M0 ≤ Fintype.card V * N := by
    rw [tasaki23GroundStateSectors_mem_iff] at hM0_mem
    refine le_trans hM0_mem.2 ?_
    rw [← tasaki23_card_filter_A_add_card_notA A]
    exact Nat.mul_le_mul_right N (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  haveI hNe : Nonempty (magConfigS V N M0) := magConfigS_nonempty_of_le_card_mul hM0_le
  -- Existence helpers from the cardinality hypotheses.
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  -- Apply Theorem 2.3 to obtain the centered Marshall-positive ground vector and global min.
  obtain ⟨μ, hper, hmin⟩ := hT23 hJ_real
    (fun x y => by
      rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJ_real x y)
    hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict hN hcardA hcardB
  obtain ⟨v, _hμc, hv_pos, hH, _huniq⟩ := hper M0 hM0_mem
  -- Name the centered ground vector `Φ⁰`.
  set Φ0 : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS V N M0 => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    with hΦ0
  refine ⟨μ, Φ0, ?_, hH, ?_, ?_, ?_⟩
  · -- `Φ⁰ ≠ 0`: it is nonzero at any centered configuration since `v > 0`.
    obtain ⟨σ0⟩ := hNe
    intro hzero
    have hval : Φ0 σ0.1 = (((marshallSignS A σ0.1).re * v σ0 : ℝ) : ℂ) := by
      rw [hΦ0]
      exact magSectorEmbedding_apply_of_mem _ σ0.2
    rw [congrFun hzero σ0.1] at hval
    have hre : (marshallSignS A σ0.1).re * v σ0 = 0 := by
      have := congrArg Complex.re hval.symm
      simpa using this
    have hsign_ne : (marshallSignS A σ0.1).re ≠ 0 := by
      rcases marshallSignS_re_eq_one_or_neg_one A σ0.1 with h | h <;> rw [h] <;> norm_num
    have hvne : v σ0 ≠ 0 := ne_of_gt (hv_pos σ0)
    exact (mul_ne_zero hsign_ne hvne) hre
  · -- Global energy minimality, transported through the named `Φ⁰`.
    intro μ' Ψ' hΨ'_ne hΨ'
    exact hmin hΨ'_ne hΨ'
  · -- `Ŝ_tot^{(3)} Φ⁰ = 0`: membership in the `magSubspaceS` with eigenvalue `|V|·N/2 − M0 = 0`.
    have hmem := magSectorEmbedding_mem_magSubspaceS
      (fun σ : magConfigS V N M0 => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    rw [mem_magSubspaceS_iff] at hmem
    rw [hΦ0, hmem, hM0_center, zero_smul]
  · -- `Ŝ_tot² Φ⁰ = S_tot(S_tot+1) • Φ⁰` via the structural per-sector Casimir lemma, fed the
    -- full-space `H`-eigen-equation `hH` directly.
    rw [hΦ0]
    exact tasaki23_pf_groundState_casimir_eq_predicted_sector A c c_toy horient hsB hM0_mem
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hv_pos hH

end LatticeSystem.Quantum
