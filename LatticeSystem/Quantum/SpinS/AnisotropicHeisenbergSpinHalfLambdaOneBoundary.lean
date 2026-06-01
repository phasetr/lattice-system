import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import LatticeSystem.Math.PerronFrobeniusFinrank

/-!
# Spin-1/2 anisotropic Hamiltonian at `lambda = 1`

This file starts the spin-1/2 `lambda = 1` boundary route for Tasaki section
2.5 Theorem 2.4.  At spin `1/2`, the single-ion term is a scalar matrix, so
`anisotropicHeisenbergS J 1 D 1` is the Heisenberg Hamiltonian plus a scalar
shift.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- At spin `1/2`, the square of `S^3` is `(1 / 4) • 1`. -/
theorem spinSOp3_one_sq_eq_quarter_smul_one :
    spinSOp3 1 * spinSOp3 1 =
      (1 / 4 : ℂ) • (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSOp3, Matrix.mul_apply] <;> norm_num

/-- The embedded spin-1/2 `S^3` square is the many-body scalar `(1 / 4) • 1`. -/
theorem onSiteS_spinSOp3_one_sq_eq_quarter_smul_one (x : Λ) :
    (onSiteS x (spinSOp3 1) * onSiteS x (spinSOp3 1) : ManyBodyOpS Λ 1) =
      (1 / 4 : ℂ) • (1 : ManyBodyOpS Λ 1) := by
  rw [onSiteS_mul_onSiteS_same, spinSOp3_one_sq_eq_quarter_smul_one,
    onSiteS_smul, onSiteS_one]

/-- In spin `1/2`, the single-ion anisotropy is the scalar
`D * |Λ| / 4`. -/
theorem singleIonAnisotropyS_spinHalf_eq_scalar (D : ℂ) :
    singleIonAnisotropyS (Λ := Λ) D 1 =
      (D * (Fintype.card Λ : ℂ) / 4) • (1 : ManyBodyOpS Λ 1) := by
  rw [singleIonAnisotropyS]
  calc
    D • (∑ x : Λ, onSiteS x (spinSOp3 1) * onSiteS x (spinSOp3 1) :
        ManyBodyOpS Λ 1) =
        D • (∑ _x : Λ, (1 / 4 : ℂ) • (1 : ManyBodyOpS Λ 1)) := by
          congr 1
          exact Finset.sum_congr rfl (fun x _ =>
            onSiteS_spinSOp3_one_sq_eq_quarter_smul_one (Λ := Λ) x)
    _ = (D * (Fintype.card Λ : ℂ) / 4) • (1 : ManyBodyOpS Λ 1) := by
          rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
          congr 1
          rw [Finset.card_univ]
          ring

/-- At spin `1/2` and `lambda = 1`, the anisotropic Hamiltonian is the
Heisenberg Hamiltonian plus the scalar single-ion shift. -/
theorem anisotropicHeisenbergS_one_D_spinHalf_eq_heisenberg_add_scalar
    (J : Λ → Λ → ℂ) (D : ℂ) :
    anisotropicHeisenbergS (Λ := Λ) J 1 D 1 =
      heisenbergHamiltonianS J 1 +
        (D * (Fintype.card Λ : ℂ) / 4) • (1 : ManyBodyOpS Λ 1) := by
  rw [anisotropicHeisenbergS_def, heisenbergHamiltonianS_def,
    singleIonAnisotropyS_spinHalf_eq_scalar]
  congr 1
  exact Finset.sum_congr rfl (fun x _ =>
    Finset.sum_congr rfl (fun y _ => by rw [spinSDotXXZ_one]))

/-- Eigenspaces are preserved by adding a scalar multiple of the identity, with
the eigenvalue shifted by the same scalar. -/
theorem eigenspace_add_smul_one_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (a μ : ℂ) :
    End.eigenspace (Matrix.toLin' (M + a • (1 : Matrix n n ℂ))) (μ + a) =
      End.eigenspace (Matrix.toLin' M) μ := by
  ext v
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff,
    Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    rw [h]

/-- The `finrank` of an eigenspace is preserved by adding a scalar multiple of
the identity, with the eigenvalue shifted by the same scalar. -/
theorem eigenspace_add_smul_one_finrank_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (a μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' (M + a • (1 : Matrix n n ℂ))) (μ + a)) =
      finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) := by
  rw [eigenspace_add_smul_one_eq]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Adding a real scalar multiple of the identity preserves Hermiticity. -/
theorem isHermitian_add_smul_one_of_real {n : Type*} [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (a : ℝ) :
    (M + (a : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  exact hM.add (Matrix.isHermitian_one.smul (Complex.conj_ofReal a))

omit [Fintype Λ] [DecidableEq Λ] in
/-- The Hermitian minimum eigenvalue shifts by the added real scalar. -/
theorem hermitianMinEigenvalue_add_smul_one {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (a : ℝ) :
    hermitianMinEigenvalue (isHermitian_add_smul_one_of_real hM a) =
      hermitianMinEigenvalue hM + a := by
  classical
  set hShift := isHermitian_add_smul_one_of_real hM a
  have h_alg_eq :
      M + (a : ℂ) • (1 : Matrix n n ℂ) =
        M + (algebraMap ℝ (Matrix n n ℂ)) a := by
    rw [← Algebra.algebraMap_eq_smul_one (R := ℂ) (A := Matrix n n ℂ) (a : ℂ),
      IsScalarTower.algebraMap_apply ℝ ℂ (Matrix n n ℂ) a]
    rfl
  have h_image_shift :
      ((Finset.univ : Finset n).image hShift.eigenvalues) =
        ((Finset.univ : Finset n).image hM.eigenvalues).image (fun lam => lam + a) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx_mem
      rw [Finset.mem_image] at hx_mem
      obtain ⟨i, _, hi⟩ := hx_mem
      have h_x_spec : x ∈ spectrum ℝ (M + (a : ℂ) • (1 : Matrix n n ℂ)) := by
        rw [hShift.spectrum_real_eq_range_eigenvalues]
        exact ⟨i, hi⟩
      rw [h_alg_eq, ← spectrum.add_singleton_eq] at h_x_spec
      obtain ⟨b, hb_mem, c, hc_mem, hxbc⟩ := h_x_spec
      rw [Set.mem_singleton_iff] at hc_mem
      rw [hM.spectrum_real_eq_range_eigenvalues] at hb_mem
      obtain ⟨j, hj⟩ := hb_mem
      rw [Finset.mem_image]
      refine ⟨hM.eigenvalues j, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      · rw [← hj, hc_mem] at hxbc
        linarith
    · intro hx_mem
      rw [Finset.mem_image] at hx_mem
      obtain ⟨y, hy_mem, hxy⟩ := hx_mem
      rw [Finset.mem_image] at hy_mem
      obtain ⟨j, _, hj⟩ := hy_mem
      have h_y_spec : hM.eigenvalues j ∈ spectrum ℝ M := by
        rw [hM.spectrum_real_eq_range_eigenvalues]
        exact ⟨j, rfl⟩
      have h_x_spec : x ∈ spectrum ℝ (M + (a : ℂ) • (1 : Matrix n n ℂ)) := by
        rw [h_alg_eq, ← spectrum.add_singleton_eq]
        refine ⟨hM.eigenvalues j, h_y_spec, a, Set.mem_singleton a, ?_⟩
        rw [← hj] at hxy
        linarith
      rw [hShift.spectrum_real_eq_range_eigenvalues] at h_x_spec
      obtain ⟨i, hi⟩ := h_x_spec
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  set S := (Finset.univ : Finset n).image hM.eigenvalues with hS_def
  set Sa := S.image (fun lam => lam + a) with hSa_def
  have hS_ne : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  have hSa_ne : Sa.Nonempty := Finset.image_nonempty.mpr hS_ne
  have h_min_eq : Sa.min' hSa_ne = S.min' hS_ne + a := by
    apply le_antisymm
    · have hmem : S.min' hS_ne + a ∈ Sa :=
        Finset.mem_image.mpr ⟨S.min' hS_ne, S.min'_mem hS_ne, rfl⟩
      exact Sa.min'_le _ hmem
    · apply Finset.le_min'
      intro z hz
      obtain ⟨w, hw_mem, hwz⟩ := Finset.mem_image.mp hz
      have hmw : S.min' hS_ne ≤ w := S.min'_le w hw_mem
      rw [← hwz]
      linarith
  have h_min_shift : hermitianMinEigenvalue hShift = Sa.min' hSa_ne := by
    unfold hermitianMinEigenvalue
    congr 1
  have h_min_M : hermitianMinEigenvalue hM = S.min' hS_ne := rfl
  rw [h_min_shift, h_min_M, h_min_eq]

/-- Spin-1/2 `lambda = 1` target uniqueness transfers from the Heisenberg
ground-state uniqueness, because the single-ion term is a scalar shift. -/
theorem spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_heisenberg
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (D : ℝ) [Nonempty (Λ → Fin (1 + 1))]
    (h_heis_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J 1))
        ((hermitianMinEigenvalue
          (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star 1) : ℝ) : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 D) : ℝ) : ℂ)) ≤
      1 := by
  classical
  set H0 := heisenbergHamiltonianS (Λ := Λ) J 1 with hH0_def
  set a : ℝ := D * (Fintype.card Λ : ℝ) / 4 with ha_def
  let hH0 : H0.IsHermitian := by
    rw [hH0_def]
    exact heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star 1
  let hShift : (H0 + (a : ℂ) • (1 : ManyBodyOpS Λ 1)).IsHermitian :=
    isHermitian_add_smul_one_of_real hH0 a
  have hscalar : (D : ℂ) * (Fintype.card Λ : ℂ) / 4 = (a : ℂ) := by
    rw [ha_def]
    norm_num
  have hH :
      anisotropicHeisenbergS (Λ := Λ) J 1 (D : ℂ) 1 =
        H0 + (a : ℂ) • (1 : ManyBodyOpS Λ 1) := by
    rw [hH0_def, anisotropicHeisenbergS_one_D_spinHalf_eq_heisenberg_add_scalar]
    rw [hscalar]
  have hmin :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 D) =
        hermitianMinEigenvalue hH0 + a := by
    simpa [hH, hShift] using hermitianMinEigenvalue_add_smul_one hH0 a
  have hfin_shift :
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (H0 + (a : ℂ) • (1 : ManyBodyOpS Λ 1)))
          (((hermitianMinEigenvalue hH0 : ℝ) : ℂ) + (a : ℂ))) =
        finrank ℂ ↥(End.eigenspace (Matrix.toLin' H0)
          ((hermitianMinEigenvalue hH0 : ℝ) : ℂ)) :=
    eigenspace_add_smul_one_finrank_eq H0 (a : ℂ)
      ((hermitianMinEigenvalue hH0 : ℝ) : ℂ)
  rw [hH, hmin]
  rw [show (((hermitianMinEigenvalue hH0 + a : ℝ) : ℂ) =
      ((hermitianMinEigenvalue hH0 : ℝ) : ℂ) + (a : ℂ)) by norm_num]
  rw [hfin_shift]
  simpa [hH0_def] using h_heis_unique

set_option linter.style.longLine false in
/-- Spin-1/2 `lambda = 1` target uniqueness from the Theorem 2.3 MLM/Casimir
endpoint.  The single-ion term is a scalar shift, so no strict-region
Perron--Frobenius parity-block irreducibility is used. -/
theorem spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (D : ℝ) [Nonempty (Λ → Fin (1 + 1))] :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 D) : ℝ) : ℂ)) ≤
      1 := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  have h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := Λ) hJ_star 1) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J 1
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * 1))) (μ : ℂ)) ≤ 1 :=
    fun μ hmin_eq =>
      tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
        (V := Λ) A 1 c_mlm hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
        hJpos hc_heis_strict h_card_eq (by norm_num) hcardA hcardB hmin_eq
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    LatticeSystem.Quantum.exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder
      (V := Λ) A 1 c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq (by norm_num) hcardA hcardB h_sector_pf
  have h_heis_unique_at_min :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J 1))
        ((hermitianMinEigenvalue
          (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star 1) : ℝ) : ℂ)) ≤ 1 := by
    rw [hμ_min]
    exact huniq_heis
  exact spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_heisenberg
    (Λ := Λ) hJ_star D h_heis_unique_at_min

set_option linter.style.longLine false in
/-- Spin-1/2 `lambda = 1` target ground states have zero total
magnetization. -/
theorem spinHalf_anisotropicHeisenbergS_lambda_one_groundState_zero_magnetization_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (D : ℝ) [Nonempty (Λ → Fin (1 + 1))]
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J 1 (D : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 D) : ℝ) : ℂ) •
        Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  classical
  have huniq :=
    spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
      (Λ := Λ) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq D
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    J 1 (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 D) : ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
