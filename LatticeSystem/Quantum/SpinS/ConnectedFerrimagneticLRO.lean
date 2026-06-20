import LatticeSystem.Quantum.SpinS.FerrimagneticLROCapstone
import LatticeSystem.Quantum.SpinS.ConnectedTheorem23
import LatticeSystem.Quantum.SpinS.ConnectedSectorIrreducible

/-!
# Tasaki §4.1 (Theorem 4.4): ferrimagnetic LRO bound for a CONNECTED coupling (existence form)

This file assembles the finite-volume ferrimagnetic long-range order bound (4.1.16) of Tasaki's
Theorem 4.4 for a *general connected* bipartite antiferromagnetic coupling, in the same
"existence form" as `ferrimagnetic_lro_completeBipartite_centered`
(`FerrimagneticLROCapstone.lean`) but dropping the complete-bipartite strict-positivity
hypothesis `hJ_pos`.

The complete-bipartite capstone takes the Theorem 2.3 ground-state data as a *complete-bipartite*
`tasaki_2_5_theorem_2_3 A N J c` `Prop` and obtains the predicted total Casimir value through
`tasaki23_pf_groundState_casimir_eq_predicted_sector`, both of which require strict positivity of
`J` on *every* cross-sublattice pair.  A connected coupling (with edges removed) cannot satisfy
that, so this file:

* takes the Theorem 2.3 ground-state *data* directly from
  `tasaki_2_5_theorem_2_3_data_of_connected` (which proves the data conclusion of the
  `tasaki_2_5_theorem_2_3` `Prop` from genuine connected hypotheses), and
* obtains the centered-sector Casimir value from the irreducibility-parameterised
  `tasaki23_pf_groundState_casimir_eq_predicted_sector_of_irreducible`, fed the connected
  irreducibility witness `isIrreducible_shiftedDressedSReMatrixOnMagSector_connected`.

Every remaining step (PR1 PSD drop, PR2 cross-term, the `Ŝ_tot^{(3)} Φ⁰ = 0` reduction, and the
predicted-Casimir coefficient bound) is graph-agnostic, so the rest of the chain (4.1.16) is reused
verbatim from the complete-bipartite capstone.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78; §2.5, Theorem 2.3, p. 42;
Problem 2.5.d, p. 40, solution pp. 498–499; E. Lieb, D. Mattis, J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

open Matrix

open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Ferrimagnetic LRO bound (existence form) for a general connected bipartite coupling.**

Tasaki's Theorem 4.4 finite-volume bound (4.1.16) on a single centered Marshall-positive ground
state `Φ⁰`, proved for a *connected* bipartite antiferromagnetic coupling `J`: `J` is real,
Hermitian, symmetric, non-negative, vanishes within a sublattice, vanishes off the connected
bipartite graph `G`, and is strictly positive on every edge of `G`.

This is the connected analogue of `ferrimagnetic_lro_completeBipartite_centered`: it replaces the
complete-bipartite strict positivity `hJ_pos` by the connected edge positivity `hJ_pos_G`
(together with connectedness `hGconn` and bipartiteness `hGbip` of `G`).  The conclusion exhibits a
nonzero centered ground state `Φ⁰` of the spin-`S` Heisenberg Hamiltonian whose unnormalized
staggered-order expectation dominates the ferrimagnetic coefficient
`(N/2)² (|A| − |B|)² ⟨Φ⁰, Φ⁰⟩`.

The proof mirrors the complete-bipartite capstone, taking the Theorem 2.3 ground-state data from the
connected *data* theorem and the centered Casimir value from the connected
irreducibility-parameterised Casimir lemma. -/
theorem ferrimagnetic_lro_connected_centered
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
  -- The center is an admissible, nonempty sector.
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_center_mem A N M0 hM0_center
  have hM0_le : M0 ≤ Fintype.card V * N := by
    rw [tasaki23GroundStateSectors_mem_iff] at hM0_mem
    refine le_trans hM0_mem.2 ?_
    rw [← tasaki23_card_filter_A_add_card_notA A]
    exact Nat.mul_le_mul_right N (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  haveI hNe : Nonempty (magConfigS V N M0) := magConfigS_nonempty_of_le_card_mul hM0_le
  -- Obtain the Theorem 2.3 ground-state *data* directly from the connected data theorem
  -- (the centered Marshall-positive ground vector + global energy minimality).  This is the
  -- connected replacement for applying the complete-bipartite Theorem 2.3 `Prop`.
  obtain ⟨μ, hper, hmin⟩ :=
    tasaki_2_5_theorem_2_3_data_of_connected A G N c c_toy horient hsB hGconn hGbip
      hc_strict_toy hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc_strict hN hcardA hcardB
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
  -- The connected irreducibility witness at the centered sector.
  have hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M0).IsIrreducible :=
    isIrreducible_shiftedDressedSReMatrixOnMagSector_connected
      (N := N) (M := M0) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc_strict
  -- `Ŝ_tot² Φ⁰ = S_tot(S_tot+1) • Φ⁰` via the *connected* irreducibility-parameterised
  -- per-sector Casimir lemma (PR3 core, replacing the complete-bipartite Casimir step).
  have hcas : (totalSpinSSquared V N).mulVec Φ0 =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ0 := by
    rw [hΦ0]
    exact tasaki23_pf_groundState_casimir_eq_predicted_sector_of_irreducible
      (N := N) (M := M0) A c c_toy horient hsB hM0_mem hJ_real hc_strict_toy
      hA_ne hB_ne hN hIrred hv_pos hH
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
  -- Assemble: coeff · nrm ≤ predictedCasimir · nrm = ⟨Ŝ²⟩ = ⟨ΣT⟩ ≤ stagTransverse ≤ ⟨(Ô)²⟩.
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
