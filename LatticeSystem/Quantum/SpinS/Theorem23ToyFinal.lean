import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence
import LatticeSystem.Quantum.SpinS.Theorem23GlobalMinimality
import LatticeSystem.Quantum.SpinS.Theorem23ToySectorEnergyLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23PredictedEnergySectorAll
import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimir
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Tasaki §2.5 Theorem 2.3 for the standard bipartite antiferromagnetic coupling

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) — TIER 6,
the final assembly for the canonical toy coupling `J = bipartiteCoupling A`.

For the standard bipartite antiferromagnetic Heisenberg coupling we close the full
`tasaki_2_5_theorem_2_3` statement (with the orientation `|¬A| ≤ |A|`).  The common
ground-state energy is the predicted minimum `μ = (bipartiteToyMinEnergyPredicted A N).re`,
realised in every admissible sector by the Theorem 2.2 Marshall-positive ground state
(#869); each sector energy equals `μ` because the toy minimum-energy bound (#3725 via the
per-sector lower bound) pins it from below and the predicted-energy witness (#3729 / #3680)
from above.  Global minimality is the sector min–max engine (#3733) with the
non-admissible bound discharged by the toy sector energy lower bound (#3734).

The only restriction relative to Tasaki's general statement is the canonical orientation
`|¬A| ≤ |A|` (the symmetric case is the mirror image) and that the coupling is the
standard bipartite one; the general-`J` minimality awaits the Lieb–Mattis monotonicity
`hOutside`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A non-empty domain underlies any non-zero real sector vector. -/
private theorem nonempty_magConfigS_of_fn_ne_zero {N M : ℕ}
    {φ : magConfigS V N M → ℝ} (hne : φ ≠ 0) : Nonempty (magConfigS V N M) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hne (funext (fun τ => (h.false τ).elim))

/-- **Per-sector toy ground state at the predicted minimum energy.** For the standard
bipartite coupling (orientation `|¬A| ≤ |A|`), in every admissible sector `M` the
Theorem 2.2 Marshall-positive ground state has energy exactly
`(bipartiteToyMinEnergyPredicted A N).re`, with the full-space eigen-equation, the dressed
real sector eigen-equation, and within-sector uniqueness. -/
private theorem toy_sector_groundState_at_predicted
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V, ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
  -- Theorem 2.2 Marshall-positive sector ground state.
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hH_M, _hsupp, huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence (M := M) A N c (bipartiteCoupling_im A)
      (fun x y => by
        rw [Complex.star_def, Complex.conj_eq_iff_im]; exact bipartiteCoupling_im A x y)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict h_intermediate
  -- The dressed real sector eigen-equation for the Marshall-positive ground state.
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
  -- `E ≤ μM` from the toy sector energy lower bound (#3734).
  have hge : E ≤ μM :=
    tasaki23_toy_sector_energy_ge_predicted A N c horient hc_strict h_intermediate
      (φ := fun σ => (marshallSignS A σ.1).re * vM σ)
      (by
        intro hzero
        have h0 := congrFun hzero (Classical.arbitrary (magConfigS V N M))
        have hp := hwM_marshall_pos (Classical.arbitrary (magConfigS V N M))
        simp only [Pi.zero_apply] at h0
        rw [h0, mul_zero] at hp
        exact lt_irrefl 0 hp)
      hReEig_M
  -- `μM ≤ E` from the predicted-energy witness (#3729) and the toy ground-energy bound (#3680).
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

/-- **Tasaki §2.5 Theorem 2.3 for the standard bipartite antiferromagnetic coupling**
(orientation `|¬A| ≤ |A|`): the full `tasaki_2_5_theorem_2_3` statement holds for
`J = bipartiteCoupling A`. -/
theorem tasaki_2_5_theorem_2_3_bipartiteToy
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card) :
    tasaki_2_5_theorem_2_3 A N (bipartiteCoupling A) c := by
  classical
  intro _hJ_real _hJ_real' _hJ_sym _hJ_nn _hJ_bipartite _hJ_pos hc_strict h_intermediate
    _hcardA _hcardB
  refine ⟨(bipartiteToyMinEnergyPredicted (Λ := V) A N).re, ?_, ?_⟩
  · -- Per-sector existence, Marshall expansion, and within-sector uniqueness.
    intro M hM _hNe
    obtain ⟨vM, hE_lt, hvM_pos, hH_M, _hReEig, huniq⟩ :=
      toy_sector_groundState_at_predicted A N c horient hc_strict h_intermediate hM
    exact ⟨vM, hE_lt, hvM_pos, hH_M, huniq⟩
  · -- Global minimality via the sector min–max engine (#3733).
    refine tasaki23_eigenvalue_ge_common A N c (bipartiteCoupling_im A)
      (fun x y => by
        rw [Complex.star_def, Complex.conj_eq_iff_im]; exact bipartiteCoupling_im A x y)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict ?_ ?_
    · -- `hcommon`: every admissible sector hosts a Marshall-positive ground state at `μ`.
      intro M hM
      haveI : Nonempty (magConfigS V N M) := by
        rw [tasaki23GroundStateSectors_mem_iff] at hM
        exact magConfigS_nonempty_of_le_card_mul
          (le_trans hM.2 (Nat.mul_le_mul_right N
            (by rw [← tasaki23_card_filter_A_add_card_notA A]
                exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))))
      obtain ⟨vM, _hE_lt, hvM_pos, _hH_M, hReEig, _huniq⟩ :=
        toy_sector_groundState_at_predicted A N c horient hc_strict h_intermediate hM
      exact ⟨vM, hvM_pos, hReEig⟩
    · -- `hOutside`: non-admissible sectors are bounded below by the toy energy bound (#3734).
      intro M _hM_non μM φ hφ_ne hφ
      haveI : Nonempty (magConfigS V N M) := nonempty_magConfigS_of_fn_ne_zero hφ_ne
      exact tasaki23_toy_sector_energy_ge_predicted A N c horient hc_strict h_intermediate
        hφ_ne hφ

end LatticeSystem.Quantum
