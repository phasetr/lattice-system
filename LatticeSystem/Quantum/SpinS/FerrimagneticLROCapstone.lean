import LatticeSystem.Quantum.SpinS.FerrimagneticLROCrossTerm
import LatticeSystem.Quantum.SpinS.FerrimagneticLROTotalSpin

/-!
# Tasaki §4.1 (Theorem 4.4): the capstone ferrimagnetic LRO bound (existence form)

This file assembles the three operator-algebraic / total-spin ingredients of Tasaki's finite-volume
proof of Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order) into the complete chain (4.1.16)
for the **complete-bipartite** family.  The pieces are

* PR1 (`FerrimagneticLROComponentAlgebra.lean`): the transverse / longitudinal split of `(Ô_Λ)²` and
  the `SU(2)`-invariance reduction of `(Ŝ_tot)²` on the kernel of `Ŝ_tot^{(3)}`;
* PR2 (`FerrimagneticLROCrossTerm.lean`): the cross-term inequality (4.1.15) on a Marshall-positive
  sector ground state;
* PR3 (`FerrimagneticLROTotalSpin.lean`): the centered ground state with the predicted total Casimir
  value `S_tot(S_tot + 1)`.

Because the existing axiom `shenQiuTian_ferrimagnetic_lro` (left untouched in
`FerrimagneticLRO.lean`) assumes a *connected*-graph coupling and quantifies over *any* ground
state — both beyond the
currently available Theorem 2.3 (which needs complete-bipartite positivity) and the
SU(2)-invariance / Schur transfer needed for the "any ground state" form — this file proves a
**new, honestly-scoped existence theorem** that takes the Theorem-2.3 ground-state data
`hT23 : tasaki_2_5_theorem_2_3 A N J c` as a hypothesis and produces *one* concrete centered
Marshall-positive ground state realizing Tasaki's bound.  The axiom is not discharged.

The chain (4.1.16) on the centered ground state `Φ⁰` reads, with `nrm = ⟨Φ⁰, Φ⁰⟩ ≥ 0`,

  `(N/2)² (|A| − |B|)² · nrm ≤ S_tot(S_tot + 1) · nrm = ⟨Φ⁰, (Ŝ_tot)² Φ⁰⟩`
                                                       `= ⟨Φ⁰, (Σ T_{x,y}) Φ⁰⟩`   (op3 Φ⁰ = 0)
                                                       `≤ ⟨Φ⁰, staggeredTransverse Φ⁰⟩` (4.1.15)
                                                       `≤ ⟨Φ⁰, (Ô_Λ)² Φ⁰⟩` (4.1.12 positivity).

We keep the unnormalized `nrm` factor on the left to avoid the square-root normalization; `Φ⁰` is
provided nonzero, so the bound is non-vacuous.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78; §2.5, Theorem 2.3, p. 42;
Problem 2.5.d, p. 40, solution pp. 498–499.
-/

namespace LatticeSystem.Quantum

open Matrix

open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Arithmetic of the predicted total spin -/

omit [DecidableEq V] in
/-- **The `A x = false` and `(! A x) = true` sublattice fibers coincide.**  Over `Bool`,
`A x = false ↔ (! A x) = true`, so the two `B`-sublattice cardinalities used by the axiom RHS
(`A x = false`) and by `tasaki23PredictedTotalSpin` (`(! A x) = true`) are equal. -/
theorem card_filter_A_false_eq_card_filter_notA (A : V → Bool) :
    (Finset.univ.filter (fun x : V => A x = false)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card := by
  classical
  congr 1
  apply Finset.filter_congr
  intro x _
  cases A x <;> simp

omit [DecidableEq V] in
/-- **Square of the predicted total spin** as the axiom RHS coefficient.
`S_tot² = (N/2)² (|A| − |B|)²`, where `S_tot = ||A| − |B|| · (N/2)`
(`tasaki23PredictedTotalSpin`) and the `B`-cardinality is taken with the `A x = false` fiber (the
form appearing in `shenQiuTian_ferrimagnetic_lro`). -/
theorem tasaki23PredictedTotalSpin_sq_eq (A : V → Bool) (N : ℕ) :
    tasaki23PredictedTotalSpin (V := V) A N ^ 2 =
      ((N : ℝ) / 2) ^ 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
          ((Finset.univ.filter (fun x : V => A x = false)).card : ℤ) : ℝ) ^ 2 := by
  classical
  unfold tasaki23PredictedTotalSpin
  rw [mul_pow, sq_abs]
  rw [card_filter_A_false_eq_card_filter_notA A]
  push_cast
  ring

omit [DecidableEq V] in
/-- **The predicted Casimir value dominates the squared total spin.**
`S_tot² ≤ S_tot(S_tot + 1)`, i.e. `tasaki23PredictedTotalSpin ^ 2 ≤ tasaki23PredictedCasimirValue`,
because `S_tot ≥ 0`. -/
theorem tasaki23PredictedTotalSpin_sq_le_casimir (A : V → Bool) (N : ℕ) :
    tasaki23PredictedTotalSpin (V := V) A N ^ 2 ≤
      tasaki23PredictedCasimirValue (V := V) A N := by
  unfold tasaki23PredictedCasimirValue
  have hnn : 0 ≤ tasaki23PredictedTotalSpin (V := V) A N := by
    unfold tasaki23PredictedTotalSpin
    positivity
  nlinarith [hnn]

/-! ## The capstone existence bound -/

/-- **Tasaki Theorem 4.4 (complete-bipartite, existence form).**  Coupling-agnostic via the
Theorem-2.3 ground-state data `hT23 : tasaki_2_5_theorem_2_3 A N J c`, there exists a concrete
centered Marshall-positive ground state `Φ⁰` of the spin-`S` Heisenberg Hamiltonian
`heisenbergHamiltonianS J N` such that

* `Φ⁰ ≠ 0`,
* `Φ⁰` is a global-minimum `H`-eigenvector (eigenvalue `μ`, with `μ ≤ μ'` for every nonzero
  `H`-eigenvalue `μ'`), and
* the squared staggered order parameter obeys Tasaki's bound (4.1.13) in the unnormalized form
  `(N/2)² (|A| − |B|)² · ⟨Φ⁰, Φ⁰⟩ ≤ ⟨Φ⁰, (Ô_Λ)² Φ⁰⟩`.

This is the assembled chain (4.1.16): the cross-term inequality (4.1.15, PR2), the longitudinal
positivity split (4.1.12, PR1), and the total-spin value `S_tot(S_tot + 1)` from Theorem 2.3 (PR3),
evaluated on the centered (`Ŝ_tot^{(3)} = 0`) sector ground state.  The existing axiom
`shenQiuTian_ferrimagnetic_lro` (connected coupling, *any* ground state) is left in place. -/
theorem ferrimagnetic_lro_completeBipartite_centered
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
    ∃ Φ0 : (V → Fin (N + 1)) → ℂ, Φ0 ≠ 0 ∧
      (∃ μ : ℝ, (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0 ∧
        (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ')) ∧
      ((N : ℝ) / 2) ^ 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
            ((Finset.univ.filter (fun x : V => A x = false)).card : ℤ) : ℝ) ^ 2 *
        (star Φ0 ⬝ᵥ Φ0).re
        ≤ (star Φ0 ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ0).re := by
  classical
  -- The center is an admissible, nonempty sector.
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
  -- Apply Theorem 2.3 to obtain the centered Marshall-positive ground vector and the global min.
  obtain ⟨μ, hper, hmin⟩ := hT23 hJ_real
    (fun x y => by
      rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJ_real x y)
    hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict hN hcardA hcardB
  obtain ⟨v, _hμc, hv_pos, hH, _huniq⟩ := hper M0 hM0_mem
  -- The concrete centered Marshall vector `Φ⁰` realizing both PR2 and PR3.
  set Φ0 : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS V N M0 => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    with hΦ0
  -- `Φ⁰` is nonzero (it is `v > 0` times a unit sign at any centered configuration).
  have hΦ0_ne : Φ0 ≠ 0 := by
    obtain ⟨σ0⟩ := hNe
    intro hzero
    have hval : Φ0 σ0.1 = (((marshallSignS A σ0.1).re * v σ0 : ℝ) : ℂ) := by
      rw [hΦ0]; exact magSectorEmbedding_apply_of_mem _ σ0.2
    rw [congrFun hzero σ0.1] at hval
    have hre : (marshallSignS A σ0.1).re * v σ0 = 0 := by
      have := congrArg Complex.re hval.symm
      simpa using this
    have hsign_ne : (marshallSignS A σ0.1).re ≠ 0 := by
      rcases marshallSignS_re_eq_one_or_neg_one A σ0.1 with h | h <;> rw [h] <;> norm_num
    exact (mul_ne_zero hsign_ne (ne_of_gt (hv_pos σ0))) hre
  -- `Ŝ_tot^{(3)} Φ⁰ = 0`: the centered magnetization sector.
  have hop3 : (totalSpinSOp3 V N).mulVec Φ0 = 0 := by
    have hmem := magSectorEmbedding_mem_magSubspaceS
      (fun σ : magConfigS V N M0 => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    rw [mem_magSubspaceS_iff] at hmem
    rw [hΦ0, hmem, hM0_center, zero_smul]
  -- `Ŝ_tot² Φ⁰ = S_tot(S_tot+1) • Φ⁰` via the structural per-sector Casimir lemma (PR3 core).
  have hcas : (totalSpinSSquared V N).mulVec Φ0 =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ0 := by
    rw [hΦ0]
    exact tasaki23_pf_groundState_casimir_eq_predicted_sector A c c_toy horient hsB hM0_mem
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hv_pos hH
  -- The squared norm `nrm = ⟨Φ⁰, Φ⁰⟩` is nonnegative.
  set nrm : ℝ := (star Φ0 ⬝ᵥ Φ0).re with hnrm
  have hnrm_nonneg : 0 ≤ nrm := by
    have hpos : (0 : ℂ) < star Φ0 ⬝ᵥ Φ0 := Matrix.dotProduct_star_self_pos_iff.mpr hΦ0_ne
    exact (Complex.le_def.mp hpos.le).1
  refine ⟨Φ0, hΦ0_ne, ⟨μ, hH, fun {μ'} {Ψ'} hΨ'_ne hΨ' => hmin hΨ'_ne hΨ'⟩, ?_⟩
  -- Bridge `Φ⁰` to PR2's required Marshall-embedding form (`marshallSignS · (v σ : ℂ)`).
  have hΦ0_marshall : Φ0 =
      magSectorEmbedding (fun σ : magConfigS V N M0 => marshallSignS A σ.1 * (v σ : ℂ)) := by
    rw [hΦ0]
    congr 1
    funext σ
    rw [Complex.ofReal_mul]
    congr 1
    exact (marshallSignS_eq_ofReal_re A σ.1).symm
  -- Step 1 (PR1): staggered transverse ≤ full squared staggered order parameter.
  have hstep1 := staggeredTransverse_expectation_le_staggeredCasimir_expectation A N Φ0
  -- Step 2 (PR2): unstaggered transverse double sum ≤ staggered transverse.
  have hstep2 :=
    noStaggeringTransverse_expectation_le_staggeredTransverse_expectation_of_marshall_sector
      A v hv_pos Φ0 hΦ0_marshall
  -- Step 3 (PR1): the unstaggered transverse double sum expectation equals `⟨Ŝ_tot² Φ⁰⟩`.
  have hstep3 : (star Φ0 ⬝ᵥ
        ((∑ x : V, ∑ y : V,
          (spinSSiteOp1 x N * spinSSiteOp1 y N +
            spinSSiteOp2 x N * spinSSiteOp2 y N)).mulVec Φ0)).re =
      (star Φ0 ⬝ᵥ (totalSpinSSquared V N).mulVec Φ0).re := by
    rw [noStaggeringTransverseSum_eq_totalSpinSSquared_sub_op3_sq V N]
    exact (totalSpinSSquared_expectation_eq_transverse_of_op3_mulVec_eq_zero V N Φ0 hop3).symm
  -- Step 4: `⟨Ŝ_tot² Φ⁰⟩ = predictedCasimir · nrm`.
  have hstep4 : (star Φ0 ⬝ᵥ (totalSpinSSquared V N).mulVec Φ0).re =
      tasaki23PredictedCasimirValue (V := V) A N * nrm := by
    rw [hcas, dotProduct_smul, smul_eq_mul, Complex.mul_re]
    rw [Complex.ofReal_re, Complex.ofReal_im, hnrm]
    ring
  -- The coefficient bound: `(N/2)² (|A| − |B|)² ≤ predictedCasimir`.
  have hcoeff : ((N : ℝ) / 2) ^ 2 *
      (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
        ((Finset.univ.filter (fun x : V => A x = false)).card : ℤ) : ℝ) ^ 2 ≤
      tasaki23PredictedCasimirValue (V := V) A N := by
    rw [← tasaki23PredictedTotalSpin_sq_eq A N]
    exact tasaki23PredictedTotalSpin_sq_le_casimir A N
  -- Assemble: coeff · nrm ≤ predictedCasimir · nrm = ⟨Ŝ²⟩ = ⟨ΣT⟩ ≤ staggeredTransverse ≤ ⟨(Ô)²⟩.
  have hcoeff_nrm : ((N : ℝ) / 2) ^ 2 *
      (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
        ((Finset.univ.filter (fun x : V => A x = false)).card : ℤ) : ℝ) ^ 2 * nrm ≤
      tasaki23PredictedCasimirValue (V := V) A N * nrm :=
    mul_le_mul_of_nonneg_right hcoeff hnrm_nonneg
  calc ((N : ℝ) / 2) ^ 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
            ((Finset.univ.filter (fun x : V => A x = false)).card : ℤ) : ℝ) ^ 2 * nrm
      ≤ tasaki23PredictedCasimirValue (V := V) A N * nrm := hcoeff_nrm
    _ = (star Φ0 ⬝ᵥ (totalSpinSSquared V N).mulVec Φ0).re := hstep4.symm
    _ = (star Φ0 ⬝ᵥ
          ((∑ x : V, ∑ y : V,
            (spinSSiteOp1 x N * spinSSiteOp1 y N +
              spinSSiteOp2 x N * spinSSiteOp2 y N)).mulVec Φ0)).re := hstep3.symm
    _ ≤ (star Φ0 ⬝ᵥ (staggeredTransverseCasimirOpS A N).mulVec Φ0).re := hstep2
    _ ≤ (star Φ0 ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ0).re := hstep1

end LatticeSystem.Quantum
