import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS
import LatticeSystem.Quantum.SpinS.BareSubmatrixBoundAtMin
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityBlockIrreducibleDNonneg
import LatticeSystem.Quantum.SpinS.DressedBareSubmatrixMinEqPFStructural
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSMLMEndpoint
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSDNonnegBoundaryCore

/-!
# General spin-S `D >= 0` boundary for the parity-block capstone

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file lifts the general spin-`S` parity-block Perron--Frobenius capstone
from `D.re > 0` to `D.re >= 0`.  The new input is the bond-only parity-block
irreducibility theorem, which avoids the single-ion strict-positive branch.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
/-! ## Deformation-path and target wrappers with `D >= 0` -/

/-- Along the Theorem 2.4 deformation path, nonnegative target `D` stays
nonnegative. -/
theorem anisotropicHeisenbergParametricPath_snd_nonneg_general
    {lam' D' : ℝ} (hD' : 0 ≤ D') {t : ℝ} (ht_nn : 0 ≤ t) :
    0 ≤ (anisotropicHeisenbergParametricPath lam' D' t).2 := by
  unfold anisotropicHeisenbergParametricPath
  change 0 ≤ t * D'
  exact mul_nonneg ht_nn hD'

set_option linter.style.longLine false in
/-- General spin-`S` anisotropic `H` eigenspace `finrank <= 2` at its global
Hermitian minimum under `D.re >= 0`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hlam_star : star lam = lam) (hD_star : star D = D) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star hlam_star hD_star) : ℝ) : ℂ)) ≤ 2 := by
  classical
  have hbound := anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional_D_nonneg_general
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne hN
  have hblock_eq := hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    (Λ := Λ) (N := N) hJim hlam hDim hJself
  have hswap_eq := axisSwapUnitarySSpinS_hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    (Λ := Λ) (N := N) hJ_star hlam_star hD_star
  have henergy_eq : (min (hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim 0))
        (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJim hlam hDim 1)) : ℝ) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star hlam_star hD_star) := by
    rw [← hblock_eq, ← hswap_eq]
  rw [henergy_eq] at hbound
  exact hbound

set_option linter.style.longLine false in
/-- General spin-`S` `finrank <= 2` at the global minimum along the
parametric path, with target `D' >= 0`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])) : ℝ) : ℂ)) ≤ 2 := by
  have hlb := anisotropicHeisenbergParametricPath_neg_one_lt_fst
    (D' := D') hlam'_lb (le_of_lt ht_pos) ht_le
  have hub := anisotropicHeisenbergParametricPath_fst_lt_one
    (D' := D') hlam'_ub ht_pos ht_le
  have hDnn := anisotropicHeisenbergParametricPath_snd_nonneg_general
    (lam' := lam') hD' (le_of_lt ht_pos)
  set lam_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
  set D_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ)
  have hlam_t_im : lam_t.im = 0 := by simp [lam_t]
  have hD_t_im : D_t.im = 0 := by simp [D_t]
  have hlam_t_re : lam_t.re = (anisotropicHeisenbergParametricPath lam' D' t).1 := by
    simp [lam_t]
  have hD_t_re : D_t.re = (anisotropicHeisenbergParametricPath lam' D' t).2 := by
    simp [D_t]
  have hlam_t_star : star lam_t = lam_t := by
    rw [Complex.star_def]; simp [lam_t]
  have hD_t_star : star D_t = D_t := by
    rw [Complex.star_def]; simp [D_t]
  have hlb_t : -1 < lam_t.re := by rw [hlam_t_re]; exact hlb
  have hub_t : lam_t.re < 1 := by rw [hlam_t_re]; exact hub
  have hDnn_t : 0 ≤ D_t.re := by rw [hD_t_re]; exact hDnn
  exact anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg_general
    A hJim hJnn hJpos hJself hJbip
    hlam_t_im hlb_t hub_t hD_t_im hDnn_t
    (hc_strict lam_t D_t) hA_ne hB_ne hN hJ_star hlam_t_star hD_t_star

set_option linter.style.longLine false in
/-- General spin-`S` deformation contradiction capstone with target
`D' >= 0`. -/
theorem anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced : (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (hne :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M lam' D' 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ_star N M_balanced lam' D') :
    False := by
  classical
  set t := sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_def
  have hmem : t ∈ perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem hJ_star N M_balanced M lam' D' hne
  have ht_nn : 0 ≤ t := hmem.2.1
  have ht_le : t ≤ 1 := hmem.2.2
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le ht_nn with hpos | h0_eq
    · exact hpos
    · exfalso
      have h_in := hmem.1
      simp only [perMCrossingSet, Set.mem_setOf_eq] at h_in
      rw [← h0_eq] at h_in
      linarith
  have h_eq_at_t := anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    hJ_star N M_balanced M lam' D' hne h_strict_gap_SU2
  have h_bal_eq_full_def := balanced_min_eq_full_at_sInf
    hJ_star N M_balanced M lam' D' hne h_GS_at_SU2 h_balanced_GS_below
  have h_bal_eq_full : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := h_bal_eq_full_def
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 N M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 N M
  have h_eq_at_t' : hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) := h_eq_at_t
  rw [h_eq_at_t'] at hΦ_M_eig
  rw [h_bal_eq_full] at hΦ_bal_eig
  have h_finrank :=
    anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_D_nonneg_general
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
      hlam'_lb hlam'_ub hD' ht_pos ht_le
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig

set_option linter.style.longLine false in
/-- General spin-`S` obligation (2) under a single SU(2)-point strict-gap
axiom, with target `D' >= 0`. -/
theorem anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam' D' 1)
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ N M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M' lam' D' 0) :
    False := by
  classical
  have axiom_GS_at_SU2 :=
    strict_GS_at_path_zero_from_strict_gap_at_SU2 (Λ := Λ) hJ_star N M_balanced
      lam' D' (fun M' _ hne => by
        haveI := ‹Nonempty (magConfigS Λ N M')›
        have := axiom_strict_gap_at_SU2 M' hne
        unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at this
        have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
        simp only [hpath] at this
        exact this)
  have hne_orig : (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_orig lam' D' ∩
      Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation_orig, ⟨by norm_num, le_refl _⟩⟩
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star N M_balanced M_orig hM_orig_ne lam' D' hne_orig
  haveI := hM_chosen_NE
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  have hM_chosen_centered_ne : (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      (M_chosen : ℂ)) ≠ 0 :=
    h_centered_nonzero M_chosen hM_chosen_range hM_chosen_ne_bal
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_chosen lam' D' 0 :=
    axiom_strict_gap_at_SU2 M_chosen hM_chosen_ne_bal
  have h_argmin : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' lam' D' ∩
        Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star N M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total := h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star N M_balanced M_chosen lam' D' hM_chosen_cross h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star N M_balanced M_chosen lam' D'
      hM_chosen_cross h_argmin)
  exact anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_D_nonneg_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_chosen h_balanced hM_chosen_centered_ne hlam'_lb hlam'_ub hD'
    hM_chosen_cross h_strict_chosen axiom_GS_at_SU2 h_below

end LatticeSystem.Quantum
