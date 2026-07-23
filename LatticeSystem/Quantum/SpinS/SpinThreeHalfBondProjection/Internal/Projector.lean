import LatticeSystem.Quantum.SpinS.SpinThreeHalfBondProjection.Internal.Tables

/-!
# The local spin-three-half maximal-spin projector certificate

This internal module lifts the frozen sector identities to the physical
two-site projector and proves its idempotence and concrete table formula.
-/

namespace LatticeSystem.Quantum.SpinThreeHalfBondProjection.Internal

open scoped ComplexOrder

/-- Restriction along a sector chart commutes with multiplication when the
left factor preserves total-down-spin sectors and the chart enumerates the
chosen sector. -/
private theorem spinThreeHalf_restrictCfg_mul
    {m : ℕ} (cfg : Fin m → (Fin 2 → Fin 4)) (n : ℕ)
    (hdown : ∀ i, spinThreeHalfDown (cfg i) = n)
    (henum : ∀ f : (Fin 2 → Fin 4) → ℂ,
      (∑ τ ∈ spinThreeHalfSector n, f τ) =
        ∑ i : Fin m, f (cfg i))
    {A B : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ}
    (hA : ∀ ρ τ,
      spinThreeHalfDown ρ ≠ spinThreeHalfDown τ → A ρ τ = 0) :
    spinThreeHalfRestrictCfg cfg (A * B) =
      spinThreeHalfRestrictCfg cfg A *
        spinThreeHalfRestrictCfg cfg B := by
  ext i j
  simp only [spinThreeHalfRestrictCfg]
  rw [spinThreeHalf_mul_apply_sector A B hA, hdown i, henum,
    Matrix.mul_apply]
  rfl

/-- Restriction along an injective chart commutes with a scalar identity
shift. -/
private theorem spinThreeHalf_restrictCfg_shift
    {m : ℕ} (cfg : Fin m → (Fin 2 → Fin 4))
    (hinj : Function.Injective cfg)
    {A : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ}
    {ATable : Matrix (Fin m) (Fin m) ℂ}
    (hA : spinThreeHalfRestrictCfg cfg A = ATable) (q : ℂ) :
    spinThreeHalfRestrictCfg cfg
        (A - q • (1 :
          Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ)) =
      ATable - q • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  ext i j
  have hentry := congrFun (congrFun hA i) j
  simp only [spinThreeHalfRestrictCfg] at hentry ⊢
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [hentry]
  simp only [hinj.eq_iff]

/-- The frozen sector-zero maximal-spin block is idempotent. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_zero_table :
    spinThreeHalfMaxSpinSectorZeroTable * spinThreeHalfMaxSpinSectorZeroTable =
      spinThreeHalfMaxSpinSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_one,
    spinThreeHalfMaxSpinSectorZeroTable, Matrix.cons_val_zero]

/-- The frozen sector-one maximal-spin block is idempotent. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_one_table :
    spinThreeHalfMaxSpinSectorOneTable * spinThreeHalfMaxSpinSectorOneTable =
      spinThreeHalfMaxSpinSectorOneTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two,
      spinThreeHalfMaxSpinSectorOneTable, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The frozen sector-two maximal-spin block is idempotent. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_two_table :
    spinThreeHalfMaxSpinSectorTwoTable * spinThreeHalfMaxSpinSectorTwoTable =
      spinThreeHalfMaxSpinSectorTwoTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three,
      spinThreeHalfMaxSpinSectorTwoTable, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring_nf at hs ⊢ <;>
    simp only [hs] <;>
    norm_num

/-- The frozen sector-three maximal-spin block is idempotent. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_three_table :
    spinThreeHalfMaxSpinSectorThreeTable * spinThreeHalfMaxSpinSectorThreeTable =
      spinThreeHalfMaxSpinSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four,
      spinThreeHalfMaxSpinSectorThreeTable, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- A frozen idempotence identity lifts to the corresponding physical
sector restriction. -/
private theorem spinThreeHalf_restrictCfg_Q_idempotent
    {m : ℕ} (cfg : Fin m → (Fin 2 → Fin 4)) (n : ℕ)
    (hdown : ∀ i, spinThreeHalfDown (cfg i) = n)
    (henum : ∀ f : (Fin 2 → Fin 4) → ℂ,
      (∑ τ ∈ spinThreeHalfSector n, f τ) =
        ∑ i : Fin m, f (cfg i))
    {QTable : Matrix (Fin m) (Fin m) ℂ}
    (hQTable :
      spinThreeHalfRestrictCfg cfg spinThreeHalfMaxSpinTable = QTable)
    (hQTableIdem : QTable * QTable = QTable) :
    spinThreeHalfRestrictCfg cfg (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg cfg spinThreeHalfMaxSpinTable := by
  calc
    spinThreeHalfRestrictCfg cfg (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
        spinThreeHalfRestrictCfg cfg spinThreeHalfMaxSpinTable *
          spinThreeHalfRestrictCfg cfg spinThreeHalfMaxSpinTable :=
      spinThreeHalf_restrictCfg_mul cfg n hdown henum
        spinThreeHalfMaxSpinTable_support
    _ = QTable * QTable := by rw [hQTable]
    _ = QTable := hQTableIdem
    _ = spinThreeHalfRestrictCfg cfg spinThreeHalfMaxSpinTable := hQTable.symm

/-- Physical idempotence restricted to total-down-spin sector zero. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_zero_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorZeroConfig 0 spinThreeHalf_down_sector_zero
    spinThreeHalf_sum_sector_zero spinThreeHalf_maxSpin_sector_zero_table
    spinThreeHalf_maxSpin_idempotent_sector_zero_table

/-- Physical idempotence restricted to total-down-spin sector one. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_one_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorOneConfig 1 spinThreeHalf_down_sector_one
    spinThreeHalf_sum_sector_one spinThreeHalf_maxSpin_sector_one_table
    spinThreeHalf_maxSpin_idempotent_sector_one_table

/-- Physical idempotence restricted to total-down-spin sector two. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_two_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorTwoConfig 2 spinThreeHalf_down_sector_two
    spinThreeHalf_sum_sector_two spinThreeHalf_maxSpin_sector_two_table
    spinThreeHalf_maxSpin_idempotent_sector_two_table

/-- Physical idempotence restricted to total-down-spin sector three. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_three_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorThreeConfig 3 spinThreeHalf_down_sector_three
    spinThreeHalf_sum_sector_three spinThreeHalf_maxSpin_sector_three_table
    spinThreeHalf_maxSpin_idempotent_sector_three_table

/-- Physical idempotence restricted to total-down-spin sector four. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_four_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorFourConfig 4 spinThreeHalf_down_sector_four
    spinThreeHalf_sum_sector_four spinThreeHalf_maxSpin_sector_four_table
    spinThreeHalf_maxSpin_idempotent_sector_two_table

/-- Physical idempotence restricted to total-down-spin sector five. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_five_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorFiveConfig 5 spinThreeHalf_down_sector_five
    spinThreeHalf_sum_sector_five spinThreeHalf_maxSpin_sector_five_table
    spinThreeHalf_maxSpin_idempotent_sector_one_table

/-- Physical idempotence restricted to total-down-spin sector six. -/
private theorem spinThreeHalf_maxSpin_idempotent_sector_six_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
        (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
        spinThreeHalfMaxSpinTable :=
  spinThreeHalf_restrictCfg_Q_idempotent
    spinThreeHalfSectorSixConfig 6 spinThreeHalf_down_sector_six
    spinThreeHalf_sum_sector_six spinThreeHalf_maxSpin_sector_six_table
    spinThreeHalf_maxSpin_idempotent_sector_zero_table

/-- A restriction equality gives the corresponding physical entry equality
when both configurations lie in the charted sector. -/
private theorem spinThreeHalf_entryOfRestriction
    {m : ℕ} (cfg : Fin m → (Fin 2 → Fin 4)) (n : ℕ)
    (hsurj : ∀ ρ, spinThreeHalfDown ρ = n → ∃ i, cfg i = ρ)
    {A B : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ}
    (hrest :
      spinThreeHalfRestrictCfg cfg A =
        spinThreeHalfRestrictCfg cfg B)
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = n)
    (hσ : spinThreeHalfDown σ = n) :
    A ρ σ = B ρ σ := by
  obtain ⟨i, rfl⟩ := hsurj ρ hρ
  obtain ⟨j, rfl⟩ := hsurj σ hσ
  simpa only [spinThreeHalfRestrictCfg] using
    congrFun (congrFun hrest i) j

/-- Physical idempotence entry identity in total-down-spin sector zero. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_zero_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 0)
    (hσ : spinThreeHalfDown σ = 0) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorZeroConfig 0 spinThreeHalf_surj_sector_zero
    spinThreeHalf_maxSpin_idempotent_sector_zero_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector one. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_one_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 1)
    (hσ : spinThreeHalfDown σ = 1) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorOneConfig 1 spinThreeHalf_surj_sector_one
    spinThreeHalf_maxSpin_idempotent_sector_one_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector two. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_two_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 2)
    (hσ : spinThreeHalfDown σ = 2) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorTwoConfig 2 spinThreeHalf_surj_sector_two
    spinThreeHalf_maxSpin_idempotent_sector_two_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector three. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_three_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 3)
    (hσ : spinThreeHalfDown σ = 3) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorThreeConfig 3 spinThreeHalf_surj_sector_three
    spinThreeHalf_maxSpin_idempotent_sector_three_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector four. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_four_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 4)
    (hσ : spinThreeHalfDown σ = 4) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorFourConfig 4 spinThreeHalf_surj_sector_four
    spinThreeHalf_maxSpin_idempotent_sector_four_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector five. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_five_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 5)
    (hσ : spinThreeHalfDown σ = 5) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorFiveConfig 5 spinThreeHalf_surj_sector_five
    spinThreeHalf_maxSpin_idempotent_sector_five_physical ρ σ hρ hσ

/-- Physical idempotence entry identity in total-down-spin sector six. -/
private theorem spinThreeHalfMaxSpinTable_idem_sector_six_entry
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 6)
    (hσ : spinThreeHalfDown σ = 6) :
    (spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable) ρ σ = spinThreeHalfMaxSpinTable ρ σ :=
  spinThreeHalf_entryOfRestriction
    spinThreeHalfSectorSixConfig 6 spinThreeHalf_surj_sector_six
    spinThreeHalf_maxSpin_idempotent_sector_six_physical ρ σ hρ hσ

/-- The physical frozen maximal-spin table is idempotent. -/
theorem spinThreeHalfMaxSpinTable_idempotent :
    spinThreeHalfMaxSpinTable * spinThreeHalfMaxSpinTable = spinThreeHalfMaxSpinTable := by
  ext ρ σ
  by_cases hdown : spinThreeHalfDown ρ = spinThreeHalfDown σ
  · have hle : spinThreeHalfDown ρ ≤ 6 := by
      have h0 := (ρ 0).isLt
      have h1 := (ρ 1).isLt
      simp only [spinThreeHalfDown]
      omega
    interval_cases hρ : spinThreeHalfDown ρ
    · exact spinThreeHalfMaxSpinTable_idem_sector_zero_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_one_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_two_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_three_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_four_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_five_entry ρ σ hρ hdown.symm
    · exact spinThreeHalfMaxSpinTable_idem_sector_six_entry ρ σ hρ hdown.symm
  · rw [spinThreeHalf_mul_support spinThreeHalfMaxSpinTable spinThreeHalfMaxSpinTable
      spinThreeHalfMaxSpinTable_support spinThreeHalfMaxSpinTable_support ρ σ hdown,
      spinThreeHalfMaxSpinTable_support ρ σ hdown]

/-- The frozen sector-zero Casimir factors multiply to its quadratic target. -/
private theorem spinThreeHalf_factor_sector_zero_table :
    (spinThreeHalfBondCasimirSectorZeroTable - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimirSectorZeroTable - (6 : ℂ) • 1) =
      spinThreeHalfFactorTargetSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_one,
    spinThreeHalfBondCasimirSectorZeroTable, spinThreeHalfFactorTargetSectorZeroTable,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.cons_val_zero]

/-- The frozen sector-zero Casimir-target product is `720` times its
maximal-spin block. -/
private theorem spinThreeHalf_mix_sector_zero_table :
    spinThreeHalfBondCasimirSectorZeroTable * spinThreeHalfFactorTargetSectorZeroTable =
      (720 : ℂ) • spinThreeHalfMaxSpinSectorZeroTable := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_one,
    spinThreeHalfBondCasimirSectorZeroTable, spinThreeHalfFactorTargetSectorZeroTable,
    spinThreeHalfMaxSpinSectorZeroTable, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero]

/-- The frozen sector-one Casimir factors multiply to its quadratic target. -/
private theorem spinThreeHalf_factor_sector_one_table :
    (spinThreeHalfBondCasimirSectorOneTable - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimirSectorOneTable - (6 : ℂ) • 1) =
      spinThreeHalfFactorTargetSectorOneTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two,
      spinThreeHalfBondCasimirSectorOneTable, spinThreeHalfFactorTargetSectorOneTable,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The frozen sector-one Casimir-target product is `720` times its
maximal-spin block. -/
private theorem spinThreeHalf_mix_sector_one_table :
    spinThreeHalfBondCasimirSectorOneTable * spinThreeHalfFactorTargetSectorOneTable =
      (720 : ℂ) • spinThreeHalfMaxSpinSectorOneTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two,
      spinThreeHalfBondCasimirSectorOneTable, spinThreeHalfFactorTargetSectorOneTable,
      spinThreeHalfMaxSpinSectorOneTable, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The frozen sector-two Casimir factors multiply to its quadratic target. -/
private theorem spinThreeHalf_factor_sector_two_table :
    (spinThreeHalfBondCasimirSectorTwoTable - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimirSectorTwoTable - (6 : ℂ) • 1) =
      spinThreeHalfFactorTargetSectorTwoTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three,
      spinThreeHalfBondCasimirSectorTwoTable, spinThreeHalfFactorTargetSectorTwoTable,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring_nf at hs ⊢ <;>
    simp only [hs] <;>
    norm_num

/-- The frozen sector-two Casimir-target product is `720` times its
maximal-spin block. -/
private theorem spinThreeHalf_mix_sector_two_table :
    spinThreeHalfBondCasimirSectorTwoTable * spinThreeHalfFactorTargetSectorTwoTable =
      (720 : ℂ) • spinThreeHalfMaxSpinSectorTwoTable := by
  have hs := spinThreeHalf_sqrt_three_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three,
      spinThreeHalfBondCasimirSectorTwoTable, spinThreeHalfFactorTargetSectorTwoTable,
      spinThreeHalfMaxSpinSectorTwoTable, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring_nf at hs ⊢ <;>
    simp only [hs] <;>
    norm_num

/-- The two Casimir factors multiply to the direct sector-three target. -/
private theorem spinThreeHalf_factor_sector_three_table :
    (spinThreeHalfBondCasimirSectorThreeTable - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimirSectorThreeTable - (6 : ℂ) • 1) =
      spinThreeHalfFactorTargetSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      spinThreeHalfBondCasimirSectorThreeTable, spinThreeHalfFactorTargetSectorThreeTable,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    norm_num

/-- The direct Casimir and target multiply to `720` times the maximal block. -/
private theorem spinThreeHalf_mix_sector_three_table :
    spinThreeHalfBondCasimirSectorThreeTable * spinThreeHalfFactorTargetSectorThreeTable =
      (720 : ℂ) • spinThreeHalfMaxSpinSectorThreeTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four,
      spinThreeHalfBondCasimirSectorThreeTable, spinThreeHalfFactorTargetSectorThreeTable,
      spinThreeHalfMaxSpinSectorThreeTable, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-zero sector. -/
private theorem spinThreeHalf_factor_sector_zero_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorZeroConfig 0
      spinThreeHalf_down_sector_zero spinThreeHalf_sum_sector_zero
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorZeroConfig
      spinThreeHalf_sector_zero_config_injective spinThreeHalf_casimir_sector_zero_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorZeroConfig
      spinThreeHalf_sector_zero_config_injective spinThreeHalf_casimir_sector_zero_table (6 : ℂ),
    spinThreeHalf_factor_sector_zero_table, spinThreeHalf_target_sector_zero_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-zero sector. -/
private theorem spinThreeHalf_mix_sector_zero_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorZeroConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorZeroConfig 0
      spinThreeHalf_down_sector_zero spinThreeHalf_sum_sector_zero
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_zero_table,
    spinThreeHalf_target_sector_zero_table,
    spinThreeHalf_mix_sector_zero_table,
    spinThreeHalf_maxSpin_sector_zero_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-one sector. -/
private theorem spinThreeHalf_factor_sector_one_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorOneConfig 1
      spinThreeHalf_down_sector_one spinThreeHalf_sum_sector_one
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorOneConfig
      spinThreeHalf_sector_one_config_injective spinThreeHalf_casimir_sector_one_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorOneConfig
      spinThreeHalf_sector_one_config_injective spinThreeHalf_casimir_sector_one_table (6 : ℂ),
    spinThreeHalf_factor_sector_one_table, spinThreeHalf_target_sector_one_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-one sector. -/
private theorem spinThreeHalf_mix_sector_one_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorOneConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorOneConfig 1
      spinThreeHalf_down_sector_one spinThreeHalf_sum_sector_one
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_one_table,
    spinThreeHalf_target_sector_one_table,
    spinThreeHalf_mix_sector_one_table,
    spinThreeHalf_maxSpin_sector_one_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-two sector. -/
private theorem spinThreeHalf_factor_sector_two_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorTwoConfig 2
      spinThreeHalf_down_sector_two spinThreeHalf_sum_sector_two
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorTwoConfig
      spinThreeHalf_sector_two_config_injective spinThreeHalf_casimir_sector_two_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorTwoConfig
      spinThreeHalf_sector_two_config_injective spinThreeHalf_casimir_sector_two_table (6 : ℂ),
    spinThreeHalf_factor_sector_two_table, spinThreeHalf_target_sector_two_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-two sector. -/
private theorem spinThreeHalf_mix_sector_two_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorTwoConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorTwoConfig 2
      spinThreeHalf_down_sector_two spinThreeHalf_sum_sector_two
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_two_table,
    spinThreeHalf_target_sector_two_table,
    spinThreeHalf_mix_sector_two_table,
    spinThreeHalf_maxSpin_sector_two_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-four sector. -/
private theorem spinThreeHalf_factor_sector_four_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorFourConfig 4
      spinThreeHalf_down_sector_four spinThreeHalf_sum_sector_four
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorFourConfig
      spinThreeHalf_sector_four_config_injective spinThreeHalf_casimir_sector_four_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorFourConfig
      spinThreeHalf_sector_four_config_injective spinThreeHalf_casimir_sector_four_table (6 : ℂ),
    spinThreeHalf_factor_sector_two_table, spinThreeHalf_target_sector_four_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-four sector. -/
private theorem spinThreeHalf_mix_sector_four_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorFourConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorFourConfig 4
      spinThreeHalf_down_sector_four spinThreeHalf_sum_sector_four
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_four_table,
    spinThreeHalf_target_sector_four_table,
    spinThreeHalf_mix_sector_two_table,
    spinThreeHalf_maxSpin_sector_four_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-five sector. -/
private theorem spinThreeHalf_factor_sector_five_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorFiveConfig 5
      spinThreeHalf_down_sector_five spinThreeHalf_sum_sector_five
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorFiveConfig
      spinThreeHalf_sector_five_config_injective spinThreeHalf_casimir_sector_five_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorFiveConfig
      spinThreeHalf_sector_five_config_injective spinThreeHalf_casimir_sector_five_table (6 : ℂ),
    spinThreeHalf_factor_sector_one_table, spinThreeHalf_target_sector_five_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-five sector. -/
private theorem spinThreeHalf_mix_sector_five_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorFiveConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorFiveConfig 5
      spinThreeHalf_down_sector_five spinThreeHalf_sum_sector_five
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_five_table,
    spinThreeHalf_target_sector_five_table,
    spinThreeHalf_mix_sector_one_table,
    spinThreeHalf_maxSpin_sector_five_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-six sector. -/
private theorem spinThreeHalf_factor_sector_six_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorSixConfig 6
      spinThreeHalf_down_sector_six spinThreeHalf_sum_sector_six
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorSixConfig
      spinThreeHalf_sector_six_config_injective spinThreeHalf_casimir_sector_six_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorSixConfig
      spinThreeHalf_sector_six_config_injective spinThreeHalf_casimir_sector_six_table (6 : ℂ),
    spinThreeHalf_factor_sector_zero_table, spinThreeHalf_target_sector_six_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-six sector. -/
private theorem spinThreeHalf_mix_sector_six_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorSixConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorSixConfig 6
      spinThreeHalf_down_sector_six spinThreeHalf_sum_sector_six
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_six_table,
    spinThreeHalf_target_sector_six_table,
    spinThreeHalf_mix_sector_zero_table,
    spinThreeHalf_maxSpin_sector_six_table]

/-- The physical Casimir factors restrict to the physical quadratic target
on the total-down-spin-three sector. -/
private theorem spinThreeHalf_factor_sector_three_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
        ((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) =
      spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
        spinThreeHalfFactorTarget := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorThreeConfig 3
      spinThreeHalf_down_sector_three spinThreeHalf_sum_sector_three
      (spinThreeHalf_shift_support (2 : ℂ)),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorThreeConfig
      spinThreeHalf_sector_three_config_injective spinThreeHalf_casimir_sector_three_table (2 : ℂ),
    spinThreeHalf_restrictCfg_shift spinThreeHalfSectorThreeConfig
      spinThreeHalf_sector_three_config_injective spinThreeHalf_casimir_sector_three_table (6 : ℂ),
    spinThreeHalf_factor_sector_three_table, spinThreeHalf_target_sector_three_table]

/-- The physical Casimir-target product restricts to `720` times the
physical maximal-spin block on the total-down-spin-three sector. -/
private theorem spinThreeHalf_mix_sector_three_physical :
    spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
        (spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) =
      (720 : ℂ) •
        spinThreeHalfRestrictCfg spinThreeHalfSectorThreeConfig
          spinThreeHalfMaxSpinTable := by
  rw [spinThreeHalf_restrictCfg_mul spinThreeHalfSectorThreeConfig 3
      spinThreeHalf_down_sector_three spinThreeHalf_sum_sector_three
      spinThreeHalfBondCasimir_support,
    spinThreeHalf_casimir_sector_three_table,
    spinThreeHalf_target_sector_three_table,
    spinThreeHalf_mix_sector_three_table,
    spinThreeHalf_maxSpin_sector_three_table]

/-- Restriction identities imply their entrywise factor-and-mix pair on
every sector enumerated by the configuration chart. -/
private theorem spinThreeHalf_combinedOfRestriction
    {m : ℕ} (cfg : Fin m → (Fin 2 → Fin 4)) (n : ℕ)
    (hsurj : ∀ ρ, spinThreeHalfDown ρ = n → ∃ i, cfg i = ρ)
    {factor target mix maxBlock :
      Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ}
    (hfactor :
      spinThreeHalfRestrictCfg cfg factor =
        spinThreeHalfRestrictCfg cfg target)
    (hmix :
      spinThreeHalfRestrictCfg cfg mix =
        (720 : ℂ) • spinThreeHalfRestrictCfg cfg maxBlock)
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = n)
    (hσ : spinThreeHalfDown σ = n) :
    factor ρ σ = target ρ σ ∧
      mix ρ σ = ((720 : ℂ) • maxBlock) ρ σ := by
  obtain ⟨i, rfl⟩ := hsurj ρ hρ
  obtain ⟨j, rfl⟩ := hsurj σ hσ
  constructor
  · simpa only [spinThreeHalfRestrictCfg] using
      congrFun (congrFun hfactor i) j
  · simpa only [spinThreeHalfRestrictCfg, Matrix.smul_apply] using
      congrFun (congrFun hmix i) j

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-zero sector. -/
private theorem spinThreeHalf_sector_zero_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 0)
    (hσ : spinThreeHalfDown σ = 0) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorZeroConfig 0 spinThreeHalf_surj_sector_zero
    spinThreeHalf_factor_sector_zero_physical spinThreeHalf_mix_sector_zero_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-one sector. -/
private theorem spinThreeHalf_sector_one_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 1)
    (hσ : spinThreeHalfDown σ = 1) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorOneConfig 1 spinThreeHalf_surj_sector_one
    spinThreeHalf_factor_sector_one_physical spinThreeHalf_mix_sector_one_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-two sector. -/
private theorem spinThreeHalf_sector_two_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 2)
    (hσ : spinThreeHalfDown σ = 2) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorTwoConfig 2 spinThreeHalf_surj_sector_two
    spinThreeHalf_factor_sector_two_physical spinThreeHalf_mix_sector_two_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-four sector. -/
private theorem spinThreeHalf_sector_four_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 4)
    (hσ : spinThreeHalfDown σ = 4) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorFourConfig 4 spinThreeHalf_surj_sector_four
    spinThreeHalf_factor_sector_four_physical spinThreeHalf_mix_sector_four_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-five sector. -/
private theorem spinThreeHalf_sector_five_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 5)
    (hσ : spinThreeHalfDown σ = 5) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorFiveConfig 5 spinThreeHalf_surj_sector_five
    spinThreeHalf_factor_sector_five_physical spinThreeHalf_mix_sector_five_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-six sector. -/
private theorem spinThreeHalf_sector_six_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 6)
    (hσ : spinThreeHalfDown σ = 6) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorSixConfig 6 spinThreeHalf_surj_sector_six
    spinThreeHalf_factor_sector_six_physical spinThreeHalf_mix_sector_six_physical ρ σ hρ hσ

/-- The physical factor and mix identities hold entrywise throughout the
total-down-spin-three sector. -/
private theorem spinThreeHalf_sector_three_combined
    (ρ σ : Fin 2 → Fin 4)
    (hρ : spinThreeHalfDown ρ = 3)
    (hσ : spinThreeHalfDown σ = 3) :
    ((((spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
          (spinThreeHalfBondCasimir - (6 : ℂ) • 1)) ρ σ =
        spinThreeHalfFactorTarget ρ σ) ∧
      ((spinThreeHalfBondCasimir * spinThreeHalfFactorTarget) ρ σ =
        ((720 : ℂ) • spinThreeHalfMaxSpinTable) ρ σ)) := by
  exact spinThreeHalf_combinedOfRestriction
    spinThreeHalfSectorThreeConfig 3 spinThreeHalf_surj_sector_three
    spinThreeHalf_factor_sector_three_physical spinThreeHalf_mix_sector_three_physical ρ σ hρ hσ

/-- The physical Casimir factor product equals its quadratic target on the
full two-site basis. -/
private theorem spinThreeHalf_factor_all :
    (spinThreeHalfBondCasimir - (2 : ℂ) • 1) *
        (spinThreeHalfBondCasimir - (6 : ℂ) • 1) =
      spinThreeHalfFactorTarget := by
  ext ρ σ
  by_cases hdown : spinThreeHalfDown ρ = spinThreeHalfDown σ
  · have hle : spinThreeHalfDown ρ ≤ 6 := by
      have h0 := (ρ 0).isLt
      have h1 := (ρ 1).isLt
      simp only [spinThreeHalfDown]
      omega
    interval_cases hρ : spinThreeHalfDown ρ
    · exact (spinThreeHalf_sector_zero_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_one_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_two_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_three_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_four_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_five_combined ρ σ hρ
        hdown.symm).1
    · exact (spinThreeHalf_sector_six_combined ρ σ hρ
        hdown.symm).1
  · rw [spinThreeHalf_factor_support ρ σ hdown,
      spinThreeHalfFactorTarget_support ρ σ hdown]

/-- The physical Casimir-target product is `720` times the maximal-spin
table on the full two-site basis. -/
private theorem spinThreeHalf_mix_all :
    spinThreeHalfBondCasimir * spinThreeHalfFactorTarget =
      (720 : ℂ) • spinThreeHalfMaxSpinTable := by
  ext ρ σ
  by_cases hdown : spinThreeHalfDown ρ = spinThreeHalfDown σ
  · have hle : spinThreeHalfDown ρ ≤ 6 := by
      have h0 := (ρ 0).isLt
      have h1 := (ρ 1).isLt
      simp only [spinThreeHalfDown]
      omega
    interval_cases hρ : spinThreeHalfDown ρ
    · exact (spinThreeHalf_sector_zero_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_one_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_two_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_three_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_four_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_five_combined ρ σ hρ
        hdown.symm).2
    · exact (spinThreeHalf_sector_six_combined ρ σ hρ
        hdown.symm).2
  · rw [spinThreeHalf_mix_support ρ σ hdown, Matrix.smul_apply,
      spinThreeHalfMaxSpinTable_support ρ σ hdown, smul_eq_mul, mul_zero]

/-- The concrete two-site spin-three-half maximal-spin projector equals the
frozen maximal-spin table. -/
theorem bondMaxSpinProjection_eq_table :
    (bondMaxSpinProjectionS (0 : Fin 2) 1 3 :
        ManyBodyOpS (Fin 2) 3) =
      spinThreeHalfMaxSpinTable := by
  have hP :
      (bondMaxSpinProjectionS (0 : Fin 2) 1 3 :
          ManyBodyOpS (Fin 2) 3) =
        ((12 : ℂ)⁻¹ • spinThreeHalfBondCasimir) *
          (((10 : ℂ)⁻¹ • (spinThreeHalfBondCasimir - (2 : ℂ) • 1)) *
            ((6 : ℂ)⁻¹ • (spinThreeHalfBondCasimir - (6 : ℂ) • 1))) := by
    simp [bondMaxSpinProjectionS, spinThreeHalfBondCasimir]
    norm_num
  rw [hP]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [spinThreeHalf_factor_all, spinThreeHalf_mix_all]
  ext ρ σ
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

end LatticeSystem.Quantum.SpinThreeHalfBondProjection.Internal
