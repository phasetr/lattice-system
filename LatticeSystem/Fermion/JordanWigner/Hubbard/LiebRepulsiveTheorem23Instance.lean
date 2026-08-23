import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFSectorCasimir
import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge

/-!
# Theorem 2.3 at the superexchange coupling, and its Casimir on the fermionic sector

The second-order effective Hamiltonian of the repulsive Hubbard model at half filling is, on the
hard-core sector, the antiferromagnetic spin-`1/2` Heisenberg Hamiltonian with the complete
bipartite coupling `J = (2 : ℂ) • bipartiteCoupling A'` up to a constant
(`secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector`,
`LiebRepulsiveFermionSpinBridge.lean`, Tasaki eq. (10.1.10)). This file feeds that coupling into
the Marshall–Lieb–Mattis theorem
`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`
(`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean`, Tasaki §2.5 Theorem 2.3) and transports the
predicted total-spin Casimir value of the resulting Marshall-positive ground state onto the
fermionic hard-core half-filled sector along
`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector`
(`LiebRepulsiveFermionSpinCasimirBridge.lean`).

## Orientation

Theorem 2.3 is stated under the canonical orientation `|¬A| ≤ |A|`, while the target Casimir
`liebRepulsiveSpinCasimir` (`LiebRepulsive.lean`) is built from the `Int.natAbs`-valued
`sublatticeImbalance` and is therefore invariant under the simultaneous swap `A ↔ Aᶜ`.
`liebOrientedSublattice` performs that swap when needed; the imbalance, and hence the predicted
Casimir value, is unchanged by it, and so is the bipartite coupling
(`bipartiteCoupling` only detects whether two sites lie on *different* sublattices).

## Scope

Only the nondegenerate bipartition `1 ≤ |A|`, `1 ≤ |Aᶜ|` is treated. The fully polarised endpoints
`A = ∅` / `A = Finset.univ` violate Theorem 2.3's own side conditions (`hsB`, `1 ≤ |¬A|`) and need
the direct fully polarised ground state `S₀ = (N + 1)/2` instead. The identification of the
fermionic sectors `configSector`/`numberSpinZSectorEuclidean`/`spinZSectorEuclidean` with one
another is likewise not treated here: every statement below stays on the
`heisenbergHamiltonianSMatrixOnMagSector` / `fermionTotalSpinSquared` side of that boundary.

## Debt

Two declarations are at reference 0. `liebOrientedSublattice_bipartiteCoupling_eq` is the adapter
rewriting the effective Hamiltonian's coupling (stated at the indicator of `A`) into the oriented
indicator Theorem 2.3 requires, and is consumed only once the two sides are assembled;
`liebRepulsive_groundState_casimir_eq_predicted` is this file's capstone.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.3, p. 42; §10.1 eq. (10.1.10), p. 345; §10.2.2 Theorem 10.4, p. 350.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-! ## Sublattice indicators and the bipartition complement -/

/-- The bipartition complement is an involution: the complement of `Aᶜ` is `A`. -/
private theorem bipartitionComplement_bipartitionComplement (A : Finset (Fin (N + 1))) :
    bipartitionComplement (bipartitionComplement A) = A := by
  ext x
  simp [bipartitionComplement]

/-- The sites carrying the indicator value `true` of a `Finset` sublattice `S` are exactly `S`. -/
private theorem liebSublattice_filter_true (S : Finset (Fin (N + 1))) :
    Finset.univ.filter (fun x : Fin (N + 1) => (decide (x ∈ S)) = true) = S := by
  ext x
  simp

/-- The sites carrying the indicator value `false` of a `Finset` sublattice `S` are exactly the
bipartition complement of `S`. -/
private theorem liebSublattice_filter_false (S : Finset (Fin (N + 1))) :
    Finset.univ.filter (fun x : Fin (N + 1) => (! decide (x ∈ S)) = true)
      = bipartitionComplement S := by
  ext x
  simp [bipartitionComplement]

/-! ## The canonically oriented sublattice -/

/-- The canonically-oriented sublattice: `A` itself if `|Aᶜ| ≤ |A|` already, otherwise its
complement `Aᶜ`. -/
noncomputable def liebOrientedSublattice (A : Finset (Fin (N + 1))) :
    Finset (Fin (N + 1)) :=
  if (bipartitionComplement A).card ≤ A.card then A else bipartitionComplement A

/-- The oriented sublattice is at least as large as its complement, `|A'ᶜ| ≤ |A'|`. -/
theorem liebOrientedSublattice_horient (A : Finset (Fin (N + 1))) :
    (bipartitionComplement (liebOrientedSublattice A)).card ≤
      (liebOrientedSublattice A).card := by
  unfold liebOrientedSublattice
  split_ifs with h
  · exact h
  · rw [bipartitionComplement_bipartitionComplement]
    omega

/-- Both the oriented sublattice and its complement are nonempty as soon as `A` and `Aᶜ` are. -/
theorem liebOrientedSublattice_card_pos (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card) :
    1 ≤ (liebOrientedSublattice A).card ∧
      1 ≤ (bipartitionComplement (liebOrientedSublattice A)).card := by
  unfold liebOrientedSublattice
  split_ifs with h
  · exact ⟨hA, hB⟩
  · rw [bipartitionComplement_bipartitionComplement]
    exact ⟨hB, hA⟩

/-- The oriented sublattice has the same sublattice imbalance as `A`: `sublatticeImbalance` is the
natural absolute value of `|A| − |Aᶜ|`, hence symmetric under the swap `A ↔ Aᶜ`. -/
theorem liebOrientedSublattice_sublatticeImbalance_eq (A : Finset (Fin (N + 1))) :
    sublatticeImbalance (liebOrientedSublattice A) = sublatticeImbalance A := by
  unfold liebOrientedSublattice
  split_ifs with h
  · rfl
  · unfold sublatticeImbalance
    rw [bipartitionComplement_bipartitionComplement]
    omega

/-- The bipartite coupling built from the oriented sublattice agrees entrywise with the one built
from `A`: `bipartiteCoupling` only detects whether the two indicators *differ*, which is unchanged
by flipping both sides of the bipartition simultaneously. -/
theorem liebOrientedSublattice_bipartiteCoupling_eq (A : Finset (Fin (N + 1))) :
    bipartiteCoupling (fun x => decide (x ∈ liebOrientedSublattice A))
      = bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A)) := by
  funext x y
  unfold bipartiteCoupling
  refine if_congr ?_ rfl rfl
  simp only [ne_eq, decide_eq_decide]
  unfold liebOrientedSublattice
  split_ifs with h
  · exact Iff.rfl
  · by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
      simp [bipartitionComplement, hx, hy]

/-- The oriented sublattice satisfies Theorem 2.3's orientation hypothesis in its `Bool`-indicator
form: the `false` fiber is no larger than the `true` fiber. -/
private theorem liebOrientedSublattice_horient_filter (A : Finset (Fin (N + 1))) :
    (Finset.univ.filter (fun x : Fin (N + 1) =>
        (! decide (x ∈ liebOrientedSublattice A)) = true)).card ≤
      (Finset.univ.filter (fun x : Fin (N + 1) =>
        (decide (x ∈ liebOrientedSublattice A)) = true)).card := by
  rw [liebSublattice_filter_true, liebSublattice_filter_false]
  exact liebOrientedSublattice_horient A

/-- Theorem 2.3's positivity side condition `0 < |¬A'| · S` at spin `S = 1/2` (`N_spin = 1`) for
the oriented sublattice of a nondegenerate bipartition. -/
private theorem liebOrientedSublattice_hsB (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card) :
    0 < ((Finset.univ.filter (fun x : Fin (N + 1) =>
      (! decide (x ∈ liebOrientedSublattice A)) = true)).card : ℝ) * ((1 : ℕ) : ℝ) / 2 := by
  have h : (1 : ℝ) ≤ ((bipartitionComplement (liebOrientedSublattice A)).card : ℝ) := by
    exact_mod_cast (liebOrientedSublattice_card_pos A hA hB).2
  rw [liebSublattice_filter_false, Nat.cast_one]
  linarith

/-! ## The coupling hypotheses at `J = (2 : ℂ) • bipartiteCoupling A'` -/

/-- Entrywise unfolding of the doubled bipartite coupling. -/
private theorem liebRepulsiveJ_apply (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    ((2 : ℂ) • bipartiteCoupling A') x y = 2 * bipartiteCoupling A' x y := rfl

/-- `J = (2 : ℂ) • bipartiteCoupling A'` has no imaginary part. -/
theorem liebRepulsiveJ_hJ_real (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    (((2 : ℂ) • bipartiteCoupling A') x y).im = 0 := by
  rw [liebRepulsiveJ_apply, Complex.mul_im, bipartiteCoupling_im]
  simp

/-- `J = (2 : ℂ) • bipartiteCoupling A'` is Hermitian entrywise (equivalently, real). -/
theorem liebRepulsiveJ_hJ_real' (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    star (((2 : ℂ) • bipartiteCoupling A') x y) = ((2 : ℂ) • bipartiteCoupling A') x y := by
  rw [Complex.star_def, Complex.conj_eq_iff_im]
  exact liebRepulsiveJ_hJ_real A' x y

/-- `J = (2 : ℂ) • bipartiteCoupling A'` is symmetric. -/
theorem liebRepulsiveJ_hJ_sym (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    ((2 : ℂ) • bipartiteCoupling A') x y = ((2 : ℂ) • bipartiteCoupling A') y x := by
  rw [liebRepulsiveJ_apply, liebRepulsiveJ_apply, bipartiteCoupling_symm]

/-- `J = (2 : ℂ) • bipartiteCoupling A'` has nonnegative real part everywhere (the coupling is
antiferromagnetic). -/
theorem liebRepulsiveJ_hJ_nn (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    0 ≤ (((2 : ℂ) • bipartiteCoupling A') x y).re := by
  have h := bipartiteCoupling_nonneg A' x y
  rw [liebRepulsiveJ_apply, Complex.mul_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

/-- `J = (2 : ℂ) • bipartiteCoupling A'` vanishes on same-sublattice pairs. -/
theorem liebRepulsiveJ_hJ_bipartite (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1))
    (h : A' x = A' y) :
    ((2 : ℂ) • bipartiteCoupling A') x y = 0 := by
  rw [liebRepulsiveJ_apply, bipartiteCoupling_eq_zero_of_same_sublattice A' h, mul_zero]

/-- `J = (2 : ℂ) • bipartiteCoupling A'` is strictly positive on every edge of the complete
bipartite graph `bipartiteCompleteGraphOf A'`: an edge joins two sites with different indicator
values, which is exactly where `bipartiteCoupling A'` takes the value `1`. -/
theorem liebRepulsiveJ_hJ_pos (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1))
    (hadj : (bipartiteCompleteGraphOf A').Adj x y) :
    0 < (((2 : ℂ) • bipartiteCoupling A') x y).re := by
  have h := bipartiteCoupling_pos_of_diff_sublattice A'
    (bipartiteCompleteGraphOf_adj_sublattice_ne hadj)
  rw [liebRepulsiveJ_apply, Complex.mul_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

/-! ## The Theorem 2.3 instance -/

/-- **Tasaki §2.5 Theorem 2.3 at the superexchange coupling.** For a bipartition of `Fin (N + 1)`,
the full Marshall–Lieb–Mattis statement `tasaki_2_5_theorem_2_3` holds at spin `S = 1/2`
(`N_spin = 1`) for the coupling `J = (2 : ℂ) • bipartiteCoupling A'` of the oriented sublattice
`A'`, at every diagonal shift `c` (the shift enters `tasaki_2_5_theorem_2_3` only through its own
hypothesis `hc_strict`, which the consumer supplies).

Unfolded, it provides: a common ground energy `μ`, for every admissible magnetization sector a
strictly Marshall-positive ground state of `heisenbergHamiltonianS J 1` supported on that sector
together with its uniqueness among Marshall-positive eigenvectors, and the global energy
minimality of `μ`.

The degenerate bipartitions `A = ∅` and `A = Finset.univ` are excluded by `hA`/`hB`. -/
theorem liebRepulsive_theorem23_instance (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card) (c : ℝ) :
    tasaki_2_5_theorem_2_3
      (fun x => decide (x ∈ liebOrientedSublattice A))
      1
      ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ liebOrientedSublattice A)))
      c := by
  obtain ⟨c_toy, hc_toy⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))
    (bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))) 1
  exact tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A)) 1 c c_toy
    (liebOrientedSublattice_horient_filter A) (liebOrientedSublattice_hsB A hA hB) hc_toy

/-! ## Casimir transport onto the fermionic hard-core sector -/

/-- The predicted total-spin Casimir value of Theorem 2.3 at spin `S = 1/2` on the oriented
sublattice is the Casimir eigenvalue `S₀ (S₀ + 1)` at `S₀ = ||A| − |Aᶜ||/2` targeted by Tasaki
Theorem 10.4. -/
theorem liebRepulsiveSpinCasimir_eq_tasaki23PredictedCasimirValue (A : Finset (Fin (N + 1))) :
    liebRepulsiveSpinCasimir A =
      (tasaki23PredictedCasimirValue (V := Fin (N + 1))
        (fun x => decide (x ∈ liebOrientedSublattice A)) 1 : ℝ) := by
  have himb : ((sublatticeImbalance A : ℕ) : ℝ)
      = |(((liebOrientedSublattice A).card : ℝ)
          - ((bipartitionComplement (liebOrientedSublattice A)).card : ℝ))| := by
    rw [← liebOrientedSublattice_sublatticeImbalance_eq A, sublatticeImbalance,
      Nat.cast_natAbs]
    push_cast
    ring_nf
  have hspin : tasaki23PredictedTotalSpin (V := Fin (N + 1))
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1
      = ((sublatticeImbalance A : ℕ) : ℝ) / 2 := by
    rw [tasaki23PredictedTotalSpin, liebSublattice_filter_true, liebSublattice_filter_false,
      himb]
    push_cast
    ring
  rw [liebRepulsiveSpinCasimir, tasaki23PredictedCasimirValue, hspin]
  push_cast
  ring

/-- **The predicted Casimir value on the fermionic hard-core half-filled sector.** For a
nondegenerate bipartition and an admissible magnetization sector (`N + 1 − nUp` admissible for the
oriented sublattice at spin `1/2`), the hard-core half-filled fermionic sector carries a nonzero
vector on which the fermionic total-spin Casimir `fermionTotalSpinSquared N` acts as the scalar
`liebRepulsiveSpinCasimir A = S₀ (S₀ + 1)`, `S₀ = ||A| − |Aᶜ||/2` (Tasaki Theorem 10.4's target
total spin).

The vector is the Marshall-positive ground state supplied by Theorem 2.3 at the superexchange
coupling (`liebRepulsive_theorem23_instance`), whose Casimir eigenvalue is the predicted one
(`tasaki23_pf_groundState_casimir_eq_predicted_sector`), read on the fermionic side along the
sector bijection of `fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector`. -/
theorem liebRepulsive_groundState_casimir_eq_predicted (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1) :
    ∃ c : configSector N (liebHardCoreHalfFillingPred N nUp) → ℂ, c ≠ 0 ∧
      ((fermionTotalSpinSquared N).submatrix
          (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
          (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)).mulVec c
        = liebRepulsiveSpinCasimir A • c := by
  classical
  haveI hne : Nonempty (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp)) :=
    magConfigS_nonempty_of_le_card_mul (by simp)
  obtain ⟨hposA, hposB⟩ := liebOrientedSublattice_card_pos A hA hB
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Fin (N + 1) =>
      (decide (x ∈ liebOrientedSublattice A)) = true)).card := by
    rw [liebSublattice_filter_true]; exact hposA
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Fin (N + 1) =>
      (! decide (x ∈ liebOrientedSublattice A)) = true)).card := by
    rw [liebSublattice_filter_false]; exact hposB
  have hA_ne : ∃ a, (decide (a ∈ liebOrientedSublattice A)) = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hposA
    exact ⟨a, by simpa using ha⟩
  have hB_ne : ∃ b, (decide (b ∈ liebOrientedSublattice A)) = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hposB
    have hb' : b ∉ liebOrientedSublattice A := by
      simpa [bipartitionComplement] using hb
    exact ⟨b, by simpa using hb'⟩
  obtain ⟨cdiag, hcdiag⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))
    ((2 : ℂ) • bipartiteCoupling
      (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))) 1
  obtain ⟨ctoy, hctoy⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))
    (bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))) 1
  obtain ⟨μ, hsector, -⟩ := liebRepulsive_theorem23_instance A hA hB cdiag
    (liebRepulsiveJ_hJ_real _) (liebRepulsiveJ_hJ_real' _) (liebRepulsiveJ_hJ_sym _)
    (liebRepulsiveJ_hJ_nn _) (liebRepulsiveJ_hJ_bipartite _) (liebRepulsiveJ_hJ_pos _)
    hcdiag le_rfl hcardA hcardB
  obtain ⟨v, -, hv_pos, hH, -⟩ := hsector _ hM
  have hcas := tasaki23_pf_groundState_casimir_eq_predicted_sector (N := 1)
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A)) cdiag ctoy
    (liebOrientedSublattice_horient_filter A) (liebOrientedSublattice_hsB A hA hB) hM
    (liebRepulsiveJ_hJ_real _) (liebRepulsiveJ_hJ_pos _) (liebRepulsiveJ_hJ_nn _)
    (liebRepulsiveJ_hJ_sym _) (liebRepulsiveJ_hJ_bipartite _) hcdiag hctoy hA_ne hB_ne
    le_rfl hv_pos hH
  set Φ : (Fin (N + 1) → Fin (1 + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) =>
      (((marshallSignS (fun x => decide (x ∈ liebOrientedSublattice A)) σ.1).re * v σ : ℝ) : ℂ))
    with hΦ
  refine ⟨fun s => Φ ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val), ?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm
      (Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))))
    rw [Equiv.apply_symm_apply, hΦ, magSectorEmbedding_apply_subtype, Pi.zero_apply] at h0
    have hre : (marshallSignS (fun x => decide (x ∈ liebOrientedSublattice A))
        (Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))).1).re
        * v (Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))) = 0 :=
      Complex.ofReal_eq_zero.mp h0
    have hvpos := hv_pos (Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp)))
    rcases marshallSignS_re_eq_one_or_neg_one
        (fun x => decide (x ∈ liebOrientedSublattice A))
        (Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))).1 with h | h <;>
      rw [h] at hre <;> linarith
  · rw [fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector N nUp hnUp,
      liebRepulsiveSpinCasimir_eq_tasaki23PredictedCasimirValue A]
    funext s
    have hsupp : ∀ σ : Fin (N + 1) → Fin (1 + 1), magSumS σ ≠ N + 1 - nUp → Φ σ = 0 := by
      intro σ hσ
      rw [hΦ]
      exact magSectorEmbedding_apply_of_not_mem _ hσ
    have hequiv : ∑ s' : configSector N (liebHardCoreHalfFillingPred N nUp),
          totalSpinSSquared (Fin (N + 1)) 1
              ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val)
              ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s').val)
            * Φ ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s').val)
        = ∑ τ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp),
          totalSpinSSquared (Fin (N + 1)) 1
              ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) τ.1 * Φ τ.1 :=
      Equiv.sum_comp (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
        (fun τ => totalSpinSSquared (Fin (N + 1)) 1
          ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) τ.1 * Φ τ.1)
    have hsubtype : ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin (N + 1) → Fin (1 + 1) => magSumS σ = N + 1 - nUp),
          totalSpinSSquared (Fin (N + 1)) 1
            ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) σ * Φ σ
        = ∑ τ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp),
          totalSpinSSquared (Fin (N + 1)) 1
            ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) τ.1 * Φ τ.1 := by
      rw [Finset.sum_subtype (F := magConfigS_instFintype) (Finset.univ.filter
        (fun σ : Fin (N + 1) → Fin (1 + 1) => magSumS σ = N + 1 - nUp))
        (p := fun σ => magSumS σ = N + 1 - nUp) (fun σ => by simp)
        (fun σ => totalSpinSSquared (Fin (N + 1)) 1
          ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) σ * Φ σ)]
      rfl
    have hfull : ∑ σ : Fin (N + 1) → Fin (1 + 1),
          totalSpinSSquared (Fin (N + 1)) 1
            ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) σ * Φ σ
        = ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin (N + 1) → Fin (1 + 1) => magSumS σ = N + 1 - nUp),
          totalSpinSSquared (Fin (N + 1)) 1
            ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) σ * Φ σ := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun σ _ hσ => ?_).symm
      rw [hsupp σ (by simpa using hσ), mul_zero]
    have hrow : ((totalSpinSSquared (Fin (N + 1)) 1).submatrix
          (fun s' => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s').val)
          (fun s' => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s').val)).mulVec
          (fun s' => Φ ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s').val)) s
        = (totalSpinSSquared (Fin (N + 1)) 1).mulVec Φ
          ((liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) := by
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
      simp only [Matrix.submatrix_apply]
      rw [hequiv, ← hsubtype, ← hfull]
    rw [hrow, hcas]
    simp

end LatticeSystem.Fermion
