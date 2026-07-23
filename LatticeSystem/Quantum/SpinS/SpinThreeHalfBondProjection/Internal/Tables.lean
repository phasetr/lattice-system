import LatticeSystem.Quantum.SpinS.GeneralAKLT

/-!
# Frozen tables for the local spin-three-half AKLT bond

This internal module constructs the sector tables and support identities used
by the local maximal-spin projector certificate.
-/

namespace LatticeSystem.Quantum.SpinThreeHalfBondProjection.Internal

open scoped ComplexOrder

/-- Total down-spin count for the sector-three frozen-table certificate. -/
def spinThreeHalfDown (σ : Fin 2 → Fin 4) : ℕ :=
  (σ 0).val + (σ 1).val

/-- Production two-site spin-3/2 Casimir for the sector-three certificate. -/
noncomputable def spinThreeHalfBondCasimir :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  bondCasimirS (0 : Fin 2) 1 3

/-- Frozen maximal-spin table used by the sector-three certificate. -/
noncomputable def spinThreeHalfMaxSpinTable :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  let s : ℂ := Real.sqrt 3
  let w : Matrix (Fin 4) (Fin 4) ℂ :=
    ![![1, s, s, 1],
      ![s, 3, 3, s],
      ![s, 3, 3, s],
      ![1, s, s, 1]]
  fun ρ τ =>
    if spinThreeHalfDown ρ = spinThreeHalfDown τ then
      (Nat.choose 6 (spinThreeHalfDown τ) : ℂ)⁻¹ *
        w (ρ 0) (ρ 1) * w (τ 0) (τ 1)
    else 0

/-- Clebsch--Gordan weight of a two-site spin-three-half configuration in
the frozen maximal-spin table. -/
noncomputable def spinThreeHalfMaxSpinWeight
    (τ : Fin 2 → Fin 4) : ℂ :=
  let s : ℂ := Real.sqrt 3
  let w : Matrix (Fin 4) (Fin 4) ℂ :=
    ![![1, s, s, 1],
      ![s, 3, 3, s],
      ![s, 3, 3, s],
      ![1, s, s, 1]]
  w (τ 0) (τ 1)

/-- Every entry of the frozen maximal-spin table factors into its two
configuration weights inside a fixed total-down-spin sector. -/
theorem spinThreeHalfMaxSpinTable_apply_weight
    (ρ τ : Fin 2 → Fin 4) :
    spinThreeHalfMaxSpinTable ρ τ =
      if spinThreeHalfDown ρ = spinThreeHalfDown τ then
        (Nat.choose 6 (spinThreeHalfDown τ) : ℂ)⁻¹ *
          spinThreeHalfMaxSpinWeight ρ * spinThreeHalfMaxSpinWeight τ
      else 0 := by
  by_cases hdown : spinThreeHalfDown ρ = spinThreeHalfDown τ
  · simp [spinThreeHalfMaxSpinTable, spinThreeHalfMaxSpinWeight, hdown]
  · simp [spinThreeHalfMaxSpinTable, hdown]

/-- The frozen maximal-spin table is Hermitian. -/
theorem spinThreeHalfMaxSpinTable_isHermitian :
    spinThreeHalfMaxSpinTable.IsHermitian := by
  have hweight_star (σ : Fin 2 → Fin 4) :
      star (spinThreeHalfMaxSpinWeight σ) = spinThreeHalfMaxSpinWeight σ := by
    obtain ⟨i, j, rfl⟩ :
        ∃ i j : Fin 4, σ = ![i, j] :=
      ⟨σ 0, σ 1, by funext k; fin_cases k <;> rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp [spinThreeHalfMaxSpinWeight, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Complex.conj_ofReal]
  have hchoose_star (n : ℕ) :
      star (n : ℂ) = (n : ℂ) := by
    simp
  unfold Matrix.IsHermitian
  ext ρ τ
  rw [Matrix.conjTranspose_apply, spinThreeHalfMaxSpinTable_apply_weight,
    spinThreeHalfMaxSpinTable_apply_weight]
  by_cases hdown : spinThreeHalfDown ρ = spinThreeHalfDown τ
  · rw [if_pos hdown.symm, if_pos hdown, star_mul', star_mul', star_inv₀,
      hchoose_star, hweight_star, hweight_star, hdown]
    ring
  · rw [if_neg (Ne.symm hdown), if_neg hdown, star_zero]

/-- Corrected spin-zero table used by the sector-three certificate. -/
private noncomputable def spinThreeHalfSpinZeroTable :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  fun ρ τ =>
    if spinThreeHalfDown ρ = 3 ∧ spinThreeHalfDown τ = 3 then
      (1 / 4 : ℂ) * (-1 : ℂ) ^ ((ρ 0).val + (τ 0).val)
    else 0

/-- Quadratic-factor target used by the sector-three certificate. -/
noncomputable def spinThreeHalfFactorTarget :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  (12 : ℂ) • spinThreeHalfSpinZeroTable + (60 : ℂ) • spinThreeHalfMaxSpinTable

/-- Configurations in a fixed total-down-spin sector. -/
def spinThreeHalfSector (n : ℕ) : Finset (Fin 2 → Fin 4) :=
  Finset.univ.filter fun σ => spinThreeHalfDown σ = n

/-- Raising/lowering formula for a production Casimir entry. -/
private theorem spinThreeHalfBondCasimir_entry_formula (σ' σ : Fin 2 → Fin 4) :
    spinThreeHalfBondCasimir σ' σ =
      (15 / 2 : ℂ) *
          (if σ' 0 = σ 0 ∧ σ' 1 = σ 1 then 1 else 0) +
        2 * ((1 / 2 : ℂ) *
            (spinSOpPlus 3 (σ' 0) (σ 0) *
                spinSOpMinus 3 (σ' 1) (σ 1) +
              spinSOpMinus 3 (σ' 0) (σ 0) *
                spinSOpPlus 3 (σ' 1) (σ 1)) +
          spinSOp3 3 (σ' 0) (σ 0) *
            spinSOp3 3 (σ' 1) (σ 1)) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hvac : ∀ k : Fin 2, k ≠ 0 → k ≠ 1 → σ' k = σ k := by
    intro k h0 h1
    fin_cases k
    · exact absurd rfl h0
    · exact absurd rfl h1
  have heq : σ' = σ ↔ σ' 0 = σ 0 ∧ σ' 1 = σ 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · exact fun h => funext (Fin.forall_fin_two.mpr h)
  simp only [spinThreeHalfBondCasimir, bondCasimirS, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, heq]
  rw [spinSDot_apply_eq_pm_3]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [onSiteS_mul_onSiteS_apply_eq hne,
    onSiteS_mul_onSiteS_apply_eq hne,
    onSiteS_mul_onSiteS_apply_eq hne]
  simp only [if_pos hvac]
  norm_num

/-- The complex square of the real square root of three is three. -/
theorem spinThreeHalf_sqrt_three_mul_self :
    (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) = 3 := by
  rw [← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The complex coercion of the real square root of four is two. -/
private theorem spinThreeHalf_sqrt_four :
    ((Real.sqrt 4 : ℝ) : ℂ) = 2 := by
  rw [show Real.sqrt 4 = 2 by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_nonneg 4]]
  norm_num

/-- The unique total-down-spin-zero configuration. -/
def spinThreeHalfSectorZeroConfig :
    Fin 1 → (Fin 2 → Fin 4) :=
  ![![0, 0]]

/-- Canonical order `01,10` of the sector-one configurations. -/
def spinThreeHalfSectorOneConfig :
    Fin 2 → (Fin 2 → Fin 4) :=
  ![![0, 1], ![1, 0]]

/-- Canonical order `02,11,20` of the sector-two configurations. -/
def spinThreeHalfSectorTwoConfig :
    Fin 3 → (Fin 2 → Fin 4) :=
  ![![0, 2], ![1, 1], ![2, 0]]

/-- Canonical order `13,22,31` of the sector-four configurations. -/
def spinThreeHalfSectorFourConfig :
    Fin 3 → (Fin 2 → Fin 4) :=
  ![![1, 3], ![2, 2], ![3, 1]]

/-- Canonical order `23,32` of the sector-five configurations. -/
def spinThreeHalfSectorFiveConfig :
    Fin 2 → (Fin 2 → Fin 4) :=
  ![![2, 3], ![3, 2]]

/-- The unique total-down-spin-six configuration. -/
def spinThreeHalfSectorSixConfig :
    Fin 1 → (Fin 2 → Fin 4) :=
  ![![3, 3]]

/-- Canonical order `03,12,21,30` of the sector-three configurations. -/
def spinThreeHalfSectorThreeConfig :
    Fin 4 → (Fin 2 → Fin 4) :=
  ![![0, 3], ![1, 2], ![2, 1], ![3, 0]]

/-- Restriction of a physical matrix along a finite configuration chart. -/
def spinThreeHalfRestrictCfg {m : ℕ}
    (cfg : Fin m → (Fin 2 → Fin 4))
    (A : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => A (cfg i) (cfg j)

/-- Frozen Casimir entries in the sector-zero block. -/
noncomputable def spinThreeHalfBondCasimirSectorZeroTable :
    Matrix (Fin 1) (Fin 1) ℂ :=
  ![![(12 : ℂ)]]

/-- Frozen maximal-spin entries in the sector-zero block. -/
noncomputable def spinThreeHalfMaxSpinSectorZeroTable :
    Matrix (Fin 1) (Fin 1) ℂ :=
  ![![(1 : ℂ)]]

/-- Frozen quadratic-target entries in the sector-zero block. -/
noncomputable def spinThreeHalfFactorTargetSectorZeroTable :
    Matrix (Fin 1) (Fin 1) ℂ :=
  ![![(60 : ℂ)]]

/-- Frozen Casimir entries in the sector-one block. -/
noncomputable def spinThreeHalfBondCasimirSectorOneTable :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(9 : ℂ), 3],
    ![3, 9]]

/-- Frozen maximal-spin entries in the sector-one block. -/
noncomputable def spinThreeHalfMaxSpinSectorOneTable :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(1 / 2 : ℂ), (1 / 2 : ℂ)],
    ![(1 / 2 : ℂ), (1 / 2 : ℂ)]]

/-- Frozen quadratic-target entries in the sector-one block. -/
noncomputable def spinThreeHalfFactorTargetSectorOneTable :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(30 : ℂ), 30],
    ![30, 30]]

/-- Frozen Casimir entries in the sector-two block. -/
noncomputable def spinThreeHalfBondCasimirSectorTwoTable :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let s : ℂ := Real.sqrt 3
  ![![(6 : ℂ), 2 * s, 0],
    ![2 * s, 8, 2 * s],
    ![0, 2 * s, 6]]

/-- Frozen maximal-spin entries in the sector-two block. -/
noncomputable def spinThreeHalfMaxSpinSectorTwoTable :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let s : ℂ := Real.sqrt 3
  ![![(1 / 5 : ℂ), (1 / 5 : ℂ) * s, (1 / 5 : ℂ)],
    ![(1 / 5 : ℂ) * s, (3 / 5 : ℂ), (1 / 5 : ℂ) * s],
    ![(1 / 5 : ℂ), (1 / 5 : ℂ) * s, (1 / 5 : ℂ)]]

/-- Frozen quadratic-target entries in the sector-two block. -/
noncomputable def spinThreeHalfFactorTargetSectorTwoTable :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let s : ℂ := Real.sqrt 3
  ![![12, 12 * s, 12],
    ![12 * s, 36, 12 * s],
    ![12, 12 * s, 12]]

/-- Direct Casimir entries in the sector-three block. -/
noncomputable def spinThreeHalfBondCasimirSectorThreeTable :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(3 : ℂ), 3, 0, 0],
    ![3, 7, 4, 0],
    ![0, 4, 7, 3],
    ![0, 0, 3, 3]]

/-- Direct maximal-spin entries in the sector-three block. -/
noncomputable def spinThreeHalfMaxSpinSectorThreeTable :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(1 / 20 : ℂ), (3 / 20 : ℂ), (3 / 20 : ℂ), (1 / 20 : ℂ)],
    ![(3 / 20 : ℂ), (9 / 20 : ℂ), (9 / 20 : ℂ), (3 / 20 : ℂ)],
    ![(3 / 20 : ℂ), (9 / 20 : ℂ), (9 / 20 : ℂ), (3 / 20 : ℂ)],
    ![(1 / 20 : ℂ), (3 / 20 : ℂ), (3 / 20 : ℂ), (1 / 20 : ℂ)]]

/-- Direct corrected spin-zero entries in the sector-three block. -/
private noncomputable def spinThreeHalfSpinZeroSectorThreeTable :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(1 / 4 : ℂ), (-1 / 4 : ℂ), (1 / 4 : ℂ), (-1 / 4 : ℂ)],
    ![(-1 / 4 : ℂ), (1 / 4 : ℂ), (-1 / 4 : ℂ), (1 / 4 : ℂ)],
    ![(1 / 4 : ℂ), (-1 / 4 : ℂ), (1 / 4 : ℂ), (-1 / 4 : ℂ)],
    ![(-1 / 4 : ℂ), (1 / 4 : ℂ), (-1 / 4 : ℂ), (1 / 4 : ℂ)]]

/-- Direct quadratic-factor target entries in the sector-three block. -/
noncomputable def spinThreeHalfFactorTargetSectorThreeTable :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(6 : ℂ), 6, 12, 0],
    ![6, 30, 24, 12],
    ![12, 24, 30, 6],
    ![0, 12, 6, 6]]

/-- The total-down-spin-zero sector contains only the all-up
configuration. -/
private theorem spinThreeHalf_sector_zero :
    spinThreeHalfSector 0 = {![0, 0]} := by
  ext τ
  simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext k
    fin_cases k
    · apply Fin.ext
      change (τ 0).val = 0
      dsimp only [spinThreeHalfDown] at h
      omega
    · apply Fin.ext
      change (τ 1).val = 0
      dsimp only [spinThreeHalfDown] at h
      omega
  · rintro rfl
    norm_num [spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The sector-zero chart has total down-spin zero. -/
theorem spinThreeHalf_down_sector_zero (i : Fin 1) :
    spinThreeHalfDown (spinThreeHalfSectorZeroConfig i) = 0 := by
  fin_cases i
  norm_num [spinThreeHalfSectorZeroConfig, spinThreeHalfDown,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A sector-zero sum is a sum over its one-element canonical chart. -/
theorem spinThreeHalf_sum_sector_zero
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 0, f τ) =
      ∑ i : Fin 1, f (spinThreeHalfSectorZeroConfig i) := by
  rw [spinThreeHalf_sector_zero, Fin.sum_univ_one]
  simp only [Finset.sum_singleton, spinThreeHalfSectorZeroConfig,
    Matrix.cons_val_zero]

/-- The one-element sector-zero chart is injective. -/
theorem spinThreeHalf_sector_zero_config_injective :
    Function.Injective spinThreeHalfSectorZeroConfig := by
  intro i j _
  exact Subsingleton.elim i j

/-- The canonical chart is surjective onto the total-down-spin-zero
sector. -/
theorem spinThreeHalf_surj_sector_zero
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 0) :
    ∃ i : Fin 1, spinThreeHalfSectorZeroConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 0 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_zero] at hmem
  simp only [Finset.mem_singleton] at hmem
  exact ⟨0, by
    simpa only [spinThreeHalfSectorZeroConfig,
      Matrix.cons_val_zero] using hmem.symm⟩

/-- The total-down-spin-one sector has the two canonical configurations
`01,10`. -/
private theorem spinThreeHalf_sector_one :
    spinThreeHalfSector 1 = {![0, 1], ![1, 0]} := by
  ext τ
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 4, τ = ![a, b] :=
    ⟨τ 0, τ 1, by funext k; fin_cases k <;> rfl⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfSector, spinThreeHalfDown, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every canonical sector-one configuration has total down-spin one. -/
theorem spinThreeHalf_down_sector_one (i : Fin 2) :
    spinThreeHalfDown (spinThreeHalfSectorOneConfig i) = 1 := by
  fin_cases i <;>
    norm_num [spinThreeHalfSectorOneConfig, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A sector-one sum is a sum over its canonical two-element chart. -/
theorem spinThreeHalf_sum_sector_one
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 1, f τ) =
      ∑ i : Fin 2, f (spinThreeHalfSectorOneConfig i) := by
  rw [spinThreeHalf_sector_one, Fin.sum_univ_two]
  norm_num [spinThreeHalfSectorOneConfig, Fin.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The canonical sector-one configuration chart is injective. -/
theorem spinThreeHalf_sector_one_config_injective :
    Function.Injective spinThreeHalfSectorOneConfig := by
  have hfirst (i : Fin 2) :
      ((spinThreeHalfSectorOneConfig i) 0).val = i.val := by
    fin_cases i <;> rfl
  intro i j h
  apply Fin.ext
  rw [← hfirst i, ← hfirst j]
  exact congrArg Fin.val (congrFun h 0)

/-- The canonical chart is surjective onto the total-down-spin-one
sector. -/
theorem spinThreeHalf_surj_sector_one
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 1) :
    ∃ i : Fin 2, spinThreeHalfSectorOneConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 1 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_one] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact ⟨0, by
      simpa only [spinThreeHalfSectorOneConfig,
        Matrix.cons_val_zero] using hmem.symm⟩
  · exact ⟨1, by
      simpa only [spinThreeHalfSectorOneConfig,
        Matrix.cons_val_one] using hmem.symm⟩

/-- The total-down-spin-two sector has the three canonical configurations
`02,11,20`. -/
private theorem spinThreeHalf_sector_two :
    spinThreeHalfSector 2 = {![0, 2], ![1, 1], ![2, 0]} := by
  ext τ
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 4, τ = ![a, b] :=
    ⟨τ 0, τ 1, by funext k; fin_cases k <;> rfl⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfSector, spinThreeHalfDown, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every canonical sector-two configuration has total down-spin two. -/
theorem spinThreeHalf_down_sector_two (i : Fin 3) :
    spinThreeHalfDown (spinThreeHalfSectorTwoConfig i) = 2 := by
  fin_cases i <;>
    norm_num [spinThreeHalfSectorTwoConfig, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- A sector-two sum is a sum over its canonical three-element chart. -/
theorem spinThreeHalf_sum_sector_two
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 2, f τ) =
      ∑ i : Fin 3, f (spinThreeHalfSectorTwoConfig i) := by
  rw [spinThreeHalf_sector_two, Fin.sum_univ_three]
  norm_num [spinThreeHalfSectorTwoConfig, Fin.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [add_assoc]

/-- The canonical sector-two configuration chart is injective. -/
theorem spinThreeHalf_sector_two_config_injective :
    Function.Injective spinThreeHalfSectorTwoConfig := by
  have hfirst (i : Fin 3) :
      ((spinThreeHalfSectorTwoConfig i) 0).val = i.val := by
    fin_cases i <;> rfl
  intro i j h
  apply Fin.ext
  rw [← hfirst i, ← hfirst j]
  exact congrArg Fin.val (congrFun h 0)

/-- The canonical chart is surjective onto the total-down-spin-two
sector. -/
theorem spinThreeHalf_surj_sector_two
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 2) :
    ∃ i : Fin 3, spinThreeHalfSectorTwoConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 2 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_two] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem | hmem
  · exact ⟨0, by
      simpa only [spinThreeHalfSectorTwoConfig,
        Matrix.cons_val_zero] using hmem.symm⟩
  · exact ⟨1, by
      simpa only [spinThreeHalfSectorTwoConfig,
        Matrix.cons_val_one] using hmem.symm⟩
  · exact ⟨2, by
      simpa only [spinThreeHalfSectorTwoConfig,
        Matrix.cons_val_two] using hmem.symm⟩

/-- The total-down-spin-four sector has the three canonical configurations
`13,22,31`. -/
private theorem spinThreeHalf_sector_four :
    spinThreeHalfSector 4 = {![1, 3], ![2, 2], ![3, 1]} := by
  ext τ
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 4, τ = ![a, b] :=
    ⟨τ 0, τ 1, by funext k; fin_cases k <;> rfl⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfSector, spinThreeHalfDown, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every canonical sector-four configuration has total down-spin four. -/
theorem spinThreeHalf_down_sector_four (i : Fin 3) :
    spinThreeHalfDown (spinThreeHalfSectorFourConfig i) = 4 := by
  fin_cases i <;>
    norm_num [spinThreeHalfSectorFourConfig, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- A sector-four sum is a sum over its canonical three-element chart. -/
theorem spinThreeHalf_sum_sector_four
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 4, f τ) =
      ∑ i : Fin 3, f (spinThreeHalfSectorFourConfig i) := by
  rw [spinThreeHalf_sector_four, Fin.sum_univ_three]
  norm_num [spinThreeHalfSectorFourConfig, Fin.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [add_assoc]

/-- The canonical sector-four configuration chart is injective. -/
theorem spinThreeHalf_sector_four_config_injective :
    Function.Injective spinThreeHalfSectorFourConfig := by
  have hfirst (i : Fin 3) :
      ((spinThreeHalfSectorFourConfig i) 0).val = i.val + 1 := by
    fin_cases i <;> rfl
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val (congrFun h 0)
  rw [hfirst i, hfirst j] at hv
  omega

/-- The canonical chart is surjective onto the total-down-spin-four
sector. -/
theorem spinThreeHalf_surj_sector_four
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 4) :
    ∃ i : Fin 3, spinThreeHalfSectorFourConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 4 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_four] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem | hmem
  · exact ⟨0, by
      simpa only [spinThreeHalfSectorFourConfig,
        Matrix.cons_val_zero] using hmem.symm⟩
  · exact ⟨1, by
      simpa only [spinThreeHalfSectorFourConfig,
        Matrix.cons_val_one] using hmem.symm⟩
  · exact ⟨2, by
      simpa only [spinThreeHalfSectorFourConfig,
        Matrix.cons_val_two] using hmem.symm⟩

/-- The total-down-spin-five sector has the two canonical configurations
`23,32`. -/
private theorem spinThreeHalf_sector_five :
    spinThreeHalfSector 5 = {![2, 3], ![3, 2]} := by
  ext τ
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 4, τ = ![a, b] :=
    ⟨τ 0, τ 1, by funext k; fin_cases k <;> rfl⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfSector, spinThreeHalfDown, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every canonical sector-five configuration has total down-spin five. -/
theorem spinThreeHalf_down_sector_five (i : Fin 2) :
    spinThreeHalfDown (spinThreeHalfSectorFiveConfig i) = 5 := by
  fin_cases i <;>
    norm_num [spinThreeHalfSectorFiveConfig, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A sector-five sum is a sum over its canonical two-element chart. -/
theorem spinThreeHalf_sum_sector_five
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 5, f τ) =
      ∑ i : Fin 2, f (spinThreeHalfSectorFiveConfig i) := by
  rw [spinThreeHalf_sector_five, Fin.sum_univ_two]
  norm_num [spinThreeHalfSectorFiveConfig, Fin.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The canonical sector-five configuration chart is injective. -/
theorem spinThreeHalf_sector_five_config_injective :
    Function.Injective spinThreeHalfSectorFiveConfig := by
  have hfirst (i : Fin 2) :
      ((spinThreeHalfSectorFiveConfig i) 0).val = i.val + 2 := by
    fin_cases i <;> rfl
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val (congrFun h 0)
  rw [hfirst i, hfirst j] at hv
  omega

/-- The canonical chart is surjective onto the total-down-spin-five
sector. -/
theorem spinThreeHalf_surj_sector_five
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 5) :
    ∃ i : Fin 2, spinThreeHalfSectorFiveConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 5 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_five] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact ⟨0, by
      simpa only [spinThreeHalfSectorFiveConfig,
        Matrix.cons_val_zero] using hmem.symm⟩
  · exact ⟨1, by
      simpa only [spinThreeHalfSectorFiveConfig,
        Matrix.cons_val_one] using hmem.symm⟩

/-- The total-down-spin-six sector contains only the all-down
configuration. -/
private theorem spinThreeHalf_sector_six :
    spinThreeHalfSector 6 = {![3, 3]} := by
  ext τ
  simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext k
    fin_cases k
    · apply Fin.ext
      change (τ 0).val = 3
      dsimp only [spinThreeHalfDown] at h
      omega
    · apply Fin.ext
      change (τ 1).val = 3
      dsimp only [spinThreeHalfDown] at h
      omega
  · rintro rfl
    norm_num [spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The sector-six chart has total down-spin six. -/
theorem spinThreeHalf_down_sector_six (i : Fin 1) :
    spinThreeHalfDown (spinThreeHalfSectorSixConfig i) = 6 := by
  fin_cases i
  norm_num [spinThreeHalfSectorSixConfig, spinThreeHalfDown,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A sector-six sum is a sum over its one-element canonical chart. -/
theorem spinThreeHalf_sum_sector_six
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 6, f τ) =
      ∑ i : Fin 1, f (spinThreeHalfSectorSixConfig i) := by
  rw [spinThreeHalf_sector_six, Fin.sum_univ_one]
  simp only [Finset.sum_singleton, spinThreeHalfSectorSixConfig,
    Matrix.cons_val_zero]

/-- The one-element sector-six chart is injective. -/
theorem spinThreeHalf_sector_six_config_injective :
    Function.Injective spinThreeHalfSectorSixConfig := by
  intro i j _
  exact Subsingleton.elim i j

/-- The canonical chart is surjective onto the total-down-spin-six
sector. -/
theorem spinThreeHalf_surj_sector_six
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 6) :
    ∃ i : Fin 1, spinThreeHalfSectorSixConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 6 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_six] at hmem
  simp only [Finset.mem_singleton] at hmem
  exact ⟨0, by
    simpa only [spinThreeHalfSectorSixConfig,
      Matrix.cons_val_zero] using hmem.symm⟩

/-- The total-down-spin-three sector has four canonical configurations. -/
private theorem spinThreeHalf_sector_three :
    spinThreeHalfSector 3 =
      {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by
  ext τ
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 4, τ = ![a, b] :=
    ⟨τ 0, τ 1, by funext k; fin_cases k <;> rfl⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfSector, spinThreeHalfDown, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Matrix multiplication may be summed over the total-down-spin sector
preserved by the left factor. -/
theorem spinThreeHalf_mul_apply_sector
    (A B : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ)
    (hA : ∀ ρ τ,
      spinThreeHalfDown ρ ≠ spinThreeHalfDown τ → A ρ τ = 0)
    (ρ σ : Fin 2 → Fin 4) :
    (A * B) ρ σ =
      ∑ τ ∈ spinThreeHalfSector (spinThreeHalfDown ρ),
        A ρ τ * B τ σ := by
  rw [Matrix.mul_apply]
  change (∑ τ ∈ Finset.univ, A ρ τ * B τ σ) =
    ∑ τ ∈ Finset.univ.filter
        (fun τ => spinThreeHalfDown τ = spinThreeHalfDown ρ),
      A ρ τ * B τ σ
  symm
  refine Finset.sum_filter_of_ne ?_
  intro τ _ hprod
  by_contra hτ
  apply hprod
  rw [hA ρ τ (Ne.symm hτ), zero_mul]

/-- A sum over the total-down-spin-three sector is a sum over its canonical
four-element basis. -/
theorem spinThreeHalf_sum_sector_three
    (f : (Fin 2 → Fin 4) → ℂ) :
    (∑ τ ∈ spinThreeHalfSector 3, f τ) =
      ∑ i : Fin 4, f (spinThreeHalfSectorThreeConfig i) := by
  rw [spinThreeHalf_sector_three, Fin.sum_univ_four]
  norm_num [spinThreeHalfSectorThreeConfig, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [add_assoc]

/-- Every canonical sector-three configuration has total down-spin three. -/
theorem spinThreeHalf_down_sector_three (i : Fin 4) :
    spinThreeHalfDown (spinThreeHalfSectorThreeConfig i) = 3 := by
  fin_cases i <;>
    norm_num [spinThreeHalfSectorThreeConfig, spinThreeHalfDown,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The canonical sector-three configuration chart is injective. -/
theorem spinThreeHalf_sector_three_config_injective :
    Function.Injective spinThreeHalfSectorThreeConfig := by
  have hfirst (i : Fin 4) :
      (spinThreeHalfSectorThreeConfig i) 0 = i := by
    fin_cases i <;> rfl
  intro i j h
  rw [← hfirst i, ← hfirst j]
  exact congrFun h 0

/-- The canonical chart is surjective onto the total-down-spin-three
sector. -/
theorem spinThreeHalf_surj_sector_three
    (τ : Fin 2 → Fin 4) (hτ : spinThreeHalfDown τ = 3) :
    ∃ i : Fin 4, spinThreeHalfSectorThreeConfig i = τ := by
  have hmem : τ ∈ spinThreeHalfSector 3 := by
    simp only [spinThreeHalfSector, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hτ
  rw [spinThreeHalf_sector_three] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · exact ⟨0, by
      simpa only [spinThreeHalfSectorThreeConfig,
        Matrix.cons_val_zero] using hmem.symm⟩
  · exact ⟨1, by
      simpa only [spinThreeHalfSectorThreeConfig,
        Matrix.cons_val_one] using hmem.symm⟩
  · exact ⟨2, by
      simpa only [spinThreeHalfSectorThreeConfig,
        Matrix.cons_val_two] using hmem.symm⟩
  · exact ⟨3, by
      simpa only [spinThreeHalfSectorThreeConfig,
        Matrix.cons_val_three] using hmem.symm⟩

/-- The physical Casimir restricts to the frozen sector-zero table. -/
theorem spinThreeHalf_casimir_sector_zero_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorZeroConfig,
    spinThreeHalfBondCasimirSectorZeroTable, spinThreeHalfBondCasimir_entry_formula,
    spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff,
    ← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The physical maximal-spin table restricts to the frozen sector-zero
table. -/
theorem spinThreeHalf_maxSpin_sector_zero_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorZeroConfig,
    spinThreeHalfMaxSpinSectorZeroTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff, Nat.choose]

/-- The corrected physical spin-zero table vanishes on the sector-zero
block. -/
private theorem spinThreeHalf_spinZero_sector_zero_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorZeroConfig,
    spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.ext_iff]

/-- The physical quadratic target restricts to the frozen sector-zero
table. -/
theorem spinThreeHalf_target_sector_zero_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorZeroTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_zero_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_zero_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfMaxSpinSectorZeroTable,
    spinThreeHalfFactorTargetSectorZeroTable, Matrix.cons_val_zero]

/-- The physical Casimir restricts to the frozen sector-one table. -/
theorem spinThreeHalf_casimir_sector_one_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorOneTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorOneConfig,
      spinThreeHalfBondCasimirSectorOneTable, spinThreeHalfBondCasimir_entry_formula,
      spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff,
      ← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The physical maximal-spin table restricts to the frozen sector-one
table. -/
theorem spinThreeHalf_maxSpin_sector_one_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorOneTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorOneConfig,
      spinThreeHalfMaxSpinSectorOneTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff, Nat.choose] <;>
    ring_nf at hs ⊢ <;>
    rw [hs] <;>
    norm_num

/-- The corrected physical spin-zero table vanishes on the sector-one
block. -/
private theorem spinThreeHalf_spinZero_sector_one_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorOneConfig,
      spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.ext_iff]

/-- The physical quadratic target restricts to the frozen sector-one
table. -/
theorem spinThreeHalf_target_sector_one_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorOneTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_one_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_one_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfMaxSpinSectorOneTable,
      spinThreeHalfFactorTargetSectorOneTable, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The physical Casimir restricts to the frozen sector-two table. -/
theorem spinThreeHalf_casimir_sector_two_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorTwoTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
      spinThreeHalfBondCasimirSectorTwoTable, spinThreeHalfBondCasimir_entry_formula,
      spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.ext_iff, ← Complex.ofReal_mul, Real.mul_self_sqrt,
      spinThreeHalf_sqrt_four] <;>
    ring

/-- The physical maximal-spin table restricts to the frozen sector-two
table. -/
theorem spinThreeHalf_maxSpin_sector_two_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorTwoTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i
  · fin_cases j
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring_nf at hs ⊢
      rw [hs]
      norm_num
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring_nf at hs ⊢
      rw [hs]
      norm_num
  · fin_cases j
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff, Nat.choose]
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
  · fin_cases j
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring_nf at hs ⊢
      rw [hs]
      norm_num
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring
    · norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
        spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
        Fin.ext_iff]
      simp only [Matrix.cons_val_two]
      norm_num [Nat.choose]
      ring_nf at hs ⊢
      rw [hs]
      norm_num

/-- The corrected physical spin-zero table vanishes on the sector-two
block. -/
private theorem spinThreeHalf_spinZero_sector_two_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorTwoConfig,
      spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff]

/-- The physical quadratic target restricts to the frozen sector-two
table. -/
theorem spinThreeHalf_target_sector_two_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorTwoTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_two_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_two_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfMaxSpinSectorTwoTable,
      spinThreeHalfFactorTargetSectorTwoTable, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

/-- The physical Casimir restricts to the shared three-dimensional frozen
table on the sector-four block. -/
theorem spinThreeHalf_casimir_sector_four_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorTwoTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFourConfig,
      spinThreeHalfBondCasimirSectorTwoTable, spinThreeHalfBondCasimir_entry_formula,
      spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.ext_iff, ← Complex.ofReal_mul, Real.mul_self_sqrt,
      spinThreeHalf_sqrt_four] <;>
    ring

/-- The physical maximal-spin table restricts to the shared
three-dimensional frozen table on the sector-four block. -/
theorem spinThreeHalf_maxSpin_sector_four_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorTwoTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFourConfig,
      spinThreeHalfMaxSpinSectorTwoTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff, Nat.choose] <;>
    ring_nf at hs ⊢ <;>
    simp only [hs] <;>
    norm_num

/-- The corrected physical spin-zero table vanishes on the sector-four
block. -/
private theorem spinThreeHalf_spinZero_sector_four_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFourConfig,
      spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff]

/-- The physical quadratic target restricts to the shared three-dimensional
frozen table on the sector-four block. -/
theorem spinThreeHalf_target_sector_four_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorTwoTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_four_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_four_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfMaxSpinSectorTwoTable,
      spinThreeHalfFactorTargetSectorTwoTable, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

/-- The physical Casimir restricts to the shared two-dimensional frozen
table on the sector-five block. -/
theorem spinThreeHalf_casimir_sector_five_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorOneTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFiveConfig,
      spinThreeHalfBondCasimirSectorOneTable, spinThreeHalfBondCasimir_entry_formula,
      spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff,
      ← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The physical maximal-spin table restricts to the shared
two-dimensional frozen table on the sector-five block. -/
theorem spinThreeHalf_maxSpin_sector_five_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorOneTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFiveConfig,
      spinThreeHalfMaxSpinSectorOneTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff, Nat.choose] <;>
    ring_nf at hs ⊢ <;>
    rw [hs] <;>
    norm_num

/-- The corrected physical spin-zero table vanishes on the sector-five
block. -/
private theorem spinThreeHalf_spinZero_sector_five_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorFiveConfig,
      spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.ext_iff]

/-- The physical quadratic target restricts to the shared two-dimensional
frozen table on the sector-five block. -/
theorem spinThreeHalf_target_sector_five_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorOneTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_five_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_five_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfMaxSpinSectorOneTable,
      spinThreeHalfFactorTargetSectorOneTable, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The physical Casimir restricts to the shared one-dimensional frozen
table on the sector-six block. -/
theorem spinThreeHalf_casimir_sector_six_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorSixConfig,
    spinThreeHalfBondCasimirSectorZeroTable, spinThreeHalfBondCasimir_entry_formula,
    spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff,
    ← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The physical maximal-spin table restricts to the shared
one-dimensional frozen table on the sector-six block. -/
theorem spinThreeHalf_maxSpin_sector_six_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorSixConfig,
    spinThreeHalfMaxSpinSectorZeroTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.ext_iff, Nat.choose]

/-- The corrected physical spin-zero table vanishes on the sector-six
block. -/
private theorem spinThreeHalf_spinZero_sector_six_zero :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig spinThreeHalfSpinZeroTable =
      (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfRestrictCfg, spinThreeHalfSectorSixConfig,
    spinThreeHalfSpinZeroTable, spinThreeHalfDown, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.ext_iff]

/-- The physical quadratic target restricts to the shared one-dimensional
frozen table on the sector-six block. -/
theorem spinThreeHalf_target_sector_six_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorZeroTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_six_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_six_zero i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i
  fin_cases j
  norm_num [spinThreeHalfMaxSpinSectorZeroTable,
    spinThreeHalfFactorTargetSectorZeroTable, Matrix.cons_val_zero]

/-- The physical Casimir restricts to the direct sector-three table. -/
theorem spinThreeHalf_casimir_sector_three_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig spinThreeHalfBondCasimir =
      spinThreeHalfBondCasimirSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg,
      spinThreeHalfSectorThreeConfig,
      spinThreeHalfBondCasimirSectorThreeTable, spinThreeHalfBondCasimir_entry_formula,
      spinSOpPlus, spinSOpMinus, spinSOp3, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff, ← Complex.ofReal_mul,
      Real.mul_self_sqrt]

/-- The physical maximal-spin table restricts to its sector-three table. -/
theorem spinThreeHalf_maxSpin_sector_three_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig spinThreeHalfMaxSpinTable =
      spinThreeHalfMaxSpinSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg,
      spinThreeHalfSectorThreeConfig,
      spinThreeHalfMaxSpinSectorThreeTable, spinThreeHalfMaxSpinTable, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff, Nat.choose]

/-- The corrected physical spin-zero table restricts to its direct table. -/
private theorem spinThreeHalf_spinZero_sector_three_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig spinThreeHalfSpinZeroTable =
      spinThreeHalfSpinZeroSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfRestrictCfg,
      spinThreeHalfSectorThreeConfig,
      spinThreeHalfSpinZeroSectorThreeTable, spinThreeHalfSpinZeroTable, spinThreeHalfDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff]

/-- The physical quadratic target restricts to its direct sector-three table. -/
theorem spinThreeHalf_target_sector_three_table :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig spinThreeHalfFactorTarget =
      spinThreeHalfFactorTargetSectorThreeTable := by
  ext i j
  have hq := congrFun (congrFun spinThreeHalf_maxSpin_sector_three_table i) j
  have hr := congrFun (congrFun spinThreeHalf_spinZero_sector_three_table i) j
  simp only [spinThreeHalfRestrictCfg] at hq hr ⊢
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hq, hr]
  fin_cases i <;> fin_cases j <;>
    norm_num [spinThreeHalfMaxSpinSectorThreeTable,
      spinThreeHalfSpinZeroSectorThreeTable, spinThreeHalfFactorTargetSectorThreeTable,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

/-- The physical Casimir preserves total-down-spin sectors. -/
theorem spinThreeHalfBondCasimir_support (ρ τ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown τ) :
    spinThreeHalfBondCasimir ρ τ = 0 := by
  have hρτ : ρ ≠ τ := by
    intro h
    exact hne (congrArg spinThreeHalfDown h)
  have hmag : magEigenvalueS τ ≠ magEigenvalueS ρ := by
    intro heig
    apply hne
    have hsum := (magEigenvalueS_eq_iff (N := 3) τ ρ).mp heig
    simpa only [magSumS, Fin.sum_univ_two, spinThreeHalfDown] using hsum.symm
  simp only [spinThreeHalfBondCasimir, bondCasimirS, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_neg hρτ,
    spinSDot_apply_eq_zero_of_mag_ne (0 : Fin 2) 1 3 hmag,
    mul_zero, add_zero]

/-- A scalar shift of the physical Casimir preserves total-down-spin
sectors. -/
theorem spinThreeHalf_shift_support (q : ℂ)
    (ρ τ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown τ) :
    (spinThreeHalfBondCasimir -
      q • (1 : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ)) ρ τ = 0 := by
  have hρτ : ρ ≠ τ := by
    intro h
    exact hne (congrArg spinThreeHalfDown h)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    spinThreeHalfBondCasimir_support ρ τ hne, if_neg hρτ, smul_eq_mul, mul_zero,
    sub_zero]

/-- The physical maximal-spin table preserves total-down-spin sectors. -/
theorem spinThreeHalfMaxSpinTable_support (ρ τ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown τ) :
    spinThreeHalfMaxSpinTable ρ τ = 0 := by
  simp only [spinThreeHalfMaxSpinTable]
  rw [if_neg hne]

/-- The corrected physical spin-zero table preserves total-down-spin
sectors. -/
private theorem spinThreeHalfSpinZeroTable_support (ρ τ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown τ) :
    spinThreeHalfSpinZeroTable ρ τ = 0 := by
  simp only [spinThreeHalfSpinZeroTable]
  rw [if_neg]
  intro h
  exact hne (h.1.trans h.2.symm)

/-- The physical quadratic target preserves total-down-spin sectors. -/
theorem spinThreeHalfFactorTarget_support (ρ τ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown τ) :
    spinThreeHalfFactorTarget ρ τ = 0 := by
  simp only [spinThreeHalfFactorTarget, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, spinThreeHalfSpinZeroTable_support ρ τ hne,
    spinThreeHalfMaxSpinTable_support ρ τ hne, mul_zero, add_zero]

/-- A product preserves total-down-spin sectors when both factors do. -/
theorem spinThreeHalf_mul_support
    (A B : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ)
    (hA : ∀ ρ τ,
      spinThreeHalfDown ρ ≠ spinThreeHalfDown τ → A ρ τ = 0)
    (hB : ∀ ρ τ,
      spinThreeHalfDown ρ ≠ spinThreeHalfDown τ → B ρ τ = 0)
    (ρ σ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown σ) :
    (A * B) ρ σ = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro τ _
  by_cases hρτ : spinThreeHalfDown ρ = spinThreeHalfDown τ
  · have hτσ : spinThreeHalfDown τ ≠ spinThreeHalfDown σ := by
      intro h
      exact hne (hρτ.trans h)
    rw [hB τ σ hτσ, mul_zero]
  · rw [hA ρ τ hρτ, zero_mul]

/-- The physical Casimir factor product preserves total-down-spin
sectors. -/
theorem spinThreeHalf_factor_support (ρ σ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown σ) :
    ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ = 0 :=
  spinThreeHalf_mul_support
    (spinThreeHalfBondCasimir - (2 : ℂ) • 1)
    (spinThreeHalfBondCasimir - (6 : ℂ) • 1)
    (spinThreeHalf_shift_support (2 : ℂ))
    (spinThreeHalf_shift_support (6 : ℂ)) ρ σ hne

/-- The physical Casimir-target product preserves total-down-spin
sectors. -/
theorem spinThreeHalf_mix_support (ρ σ : Fin 2 → Fin 4)
    (hne : spinThreeHalfDown ρ ≠ spinThreeHalfDown σ) :
    (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ = 0 :=
  spinThreeHalf_mul_support spinThreeHalfBondCasimir
    spinThreeHalfFactorTarget spinThreeHalfBondCasimir_support
    spinThreeHalfFactorTarget_support ρ σ hne


end LatticeSystem.Quantum.SpinThreeHalfBondProjection.Internal
