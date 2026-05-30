import LatticeSystem.Quantum.SpinS.MultiSiteDot

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# `spinSDot` off-diagonal matrix elements on raising/lowering pairs
(build-speed companion)

Build-speed companion to `MultiSiteDot.lean`. Hosts the trailing
section "Off-diagonal `Ŝ_x · Ŝ_y` matrix elements on raising/
lowering pairs" plus the various vanishing variants for
off-`{x, y}`-agree configurations (originally lines 466..870 of
the parent file).

Splitting these blocks out drops the parent from ~870 lines to
~465 lines.

Direct consumers of moved names
(`Heisenberg.lean`, `RaiseLower.lean`, `DressedHeisenberg.lean`,
`DressedHeisenbergOffXY.lean`) updated to additionally import
this companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Off-diagonal `Ŝ_x · Ŝ_y` matrix elements on raising/lowering pairs -/

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}`,
the matrix element of `Ŝ_x · Ŝ_y` has non-negative real part on the
raising/lowering pair `σ_x = σ'_x + 1, σ_y + 1 = σ'_y`.

The `S^+_x ⊗ S^-_y` term contributes a positive `√(...) × √(...)`,
the `S^-_x ⊗ S^+_y` term vanishes (wrong direction), and the
`S^3_x ⊗ S^3_y` term vanishes (off-diagonal in `S^3`). -/
theorem spinSDot_apply_re_nonneg_of_raising_lowering_x
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Complex.add_re]
  rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h12re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have h12im : ((1 / 2 : ℂ)).im = 0 := by norm_num
  rw [h12re, h12im, zero_mul, sub_zero]
  have hσ'x : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  have h3eq : (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
      : ManyBodyOpS Λ N) σ' σ = 0 := by
    rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
    rw [show spinSOp3 N (σ' x) (σ x) = 0 from
      Matrix.diagonal_apply_ne _ hσ'x]
    ring
  rw [h3eq]
  simp
  positivity

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}` with
`σ' x ≠ σ x`, the `S^3 ⊗ S^3` part of `Ŝ_x · Ŝ_y` vanishes, so the
matrix element collapses to the `(1/2)(S+ S- + S- S+)` part. -/
theorem spinSDot_apply_eq_pm_only_of_off_diag_at_x
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσx : σ' x ≠ σ x) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
            : ManyBodyOpS Λ N) σ' σ +
          (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
            : ManyBodyOpS Λ N) σ' σ) := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_x
    hxy h hσx]
  ring

/-- Symmetric (vanishes by `σ' y ≠ σ y`). -/
theorem spinSDot_apply_eq_pm_only_of_off_diag_at_y
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσy : σ' y ≠ σ y) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
            : ManyBodyOpS Λ N) σ' σ +
          (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
            : ManyBodyOpS Λ N) σ' σ) := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_y
    hxy h hσy]
  ring

/-- **Explicit off-diagonal `Ŝ_x · Ŝ_y` matrix element** on a two-site
raising/lowering pair. For `x ≠ y` and `σ', σ` agreeing off `{x, y}`
with the raising shift at `x` (`σ_x = σ'_x + 1`) and lowering shift at
`y` (`σ_y + 1 = σ'_y`), the matrix element equals
`(1/2) · √(σ_x · (N - σ_x + 1)) · √((N - σ_y) · (σ_y + 1))`,
a positive real number.

The `S^3 ⊗ S^3` part vanishes (off-diagonal in `S^3`); the
`S^-_x ⊗ S^+_y` part vanishes (wrong direction at `x`); only the
`S^+_x ⊗ S^-_y` term contributes. -/
theorem spinSDot_apply_eq_raising_lowering_explicit
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((Real.sqrt (((σ x).val : ℝ) *
            ((N : ℝ) - (σ x).val + 1)) : ℝ) *
          (Real.sqrt (((N : ℝ) - (σ y).val) *
            ((σ y).val + 1)) : ℝ)) := by
  have hσx : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hσx]
  -- Now we have (1/2) * ((S+_x S-_y) σ' σ + (S-_x S+_y) σ' σ).
  -- (S-_x S+_y) σ' σ = 0 from raising at x.
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_raising_x
    hxy h hx]
  -- (S+_x S-_y) σ' σ = (S+)(σ'x σx) * (S-)(σ'y σy).
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpPlus_apply_raise N hx, spinSOpMinus_apply_lower N hy]
  ring

/-- Symmetric: lowering at `x` and raising at `y`. -/
theorem spinSDot_apply_eq_lowering_raising_explicit
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((Real.sqrt (((N : ℝ) - (σ x).val) *
            ((σ x).val + 1)) : ℝ) *
          (Real.sqrt (((σ y).val : ℝ) *
            ((N : ℝ) - (σ y).val + 1)) : ℝ)) := by
  have hσx : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hσx]
  -- (S+_x S-_y) σ' σ = 0 from lowering at x (S+ wrong direction).
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_lowering_x
    hxy h hx]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpMinus_apply_lower N hx, spinSOpPlus_apply_raise N hy]
  ring


/-- Symmetric: for `x ≠ y` and configurations `σ', σ` agreeing off
`{x, y}`, the matrix element of `Ŝ_x · Ŝ_y` has non-negative real
part on the lowering/raising pair `(σ x).val + 1 = (σ' x).val`. -/
theorem spinSDot_apply_re_nonneg_of_raising_lowering_y
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Complex.add_re]
  rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h12re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have h12im : ((1 / 2 : ℂ)).im = 0 := by norm_num
  rw [h12re, h12im, zero_mul, sub_zero]
  have hσ'x : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  have h3eq : (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
      : ManyBodyOpS Λ N) σ' σ = 0 := by
    rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
    rw [show spinSOp3 N (σ' x) (σ x) = 0 from
      Matrix.diagonal_apply_ne _ hσ'x]
    ring
  rw [h3eq]
  simp
  positivity


/-- **One-site difference vanishing**: for `x ≠ y` and configurations
`σ', σ` agreeing off a single site `z`, the matrix element of
`Ŝ_x · Ŝ_y` vanishes. (Two-site operators cannot connect
single-site differences — magnetization conservation at the
matrix-element level.)

Cases:
- `z ∉ {x, y}`: the off-pair difference site forces vanishing.
- `z ∈ {x, y}`: σ' σ agree at the *other* site of `{x, y}`, but
  S^- and S^+ have no diagonal entries, and S^3_z has off-diagonal
  zero, so all three axis terms vanish. -/
theorem spinSDot_apply_eq_zero_of_one_site_diff
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hzx : z = x
  · subst hzx
    have hy : σ' y = σ y := hagree y (Ne.symm hxy)
    have h2agree : ∀ k, k ≠ z → k ≠ y → σ' k = σ k := fun k hkz _ => hagree k hkz
    rw [spinSDot_apply_of_off_two_site_agree hxy N h2agree]
    rw [show spinSOp1 N (σ' z) (σ z) * spinSOp1 N (σ' y) (σ y) =
        spinSOp1 N (σ' z) (σ z) * 0 from by
      rw [hy, spinSOp1_apply_diag]]
    rw [show spinSOp2 N (σ' z) (σ z) * spinSOp2 N (σ' y) (σ y) =
        spinSOp2 N (σ' z) (σ z) * 0 from by
      rw [hy, spinSOp2_apply_diag]]
    rw [show spinSOp3 N (σ' z) (σ z) * spinSOp3 N (σ' y) (σ y) =
        0 * spinSOp3 N (σ' y) (σ y) from by
      rw [show spinSOp3 N (σ' z) (σ z) = 0 from
        Matrix.diagonal_apply_ne _ hz]]
    ring
  · by_cases hzy : z = y
    · subst hzy
      have hx : σ' x = σ x := hagree x hxy
      have h2agree : ∀ k, k ≠ x → k ≠ z → σ' k = σ k := fun k _ hkz => hagree k hkz
      rw [spinSDot_apply_of_off_two_site_agree hxy N h2agree]
      rw [show spinSOp1 N (σ' x) (σ x) * spinSOp1 N (σ' z) (σ z) =
          0 * spinSOp1 N (σ' z) (σ z) from by
        rw [hx, spinSOp1_apply_diag]]
      rw [show spinSOp2 N (σ' x) (σ x) * spinSOp2 N (σ' z) (σ z) =
          0 * spinSOp2 N (σ' z) (σ z) from by
        rw [hx, spinSOp2_apply_diag]]
      rw [show spinSOp3 N (σ' x) (σ x) * spinSOp3 N (σ' z) (σ z) =
          spinSOp3 N (σ' x) (σ x) * 0 from by
        rw [show spinSOp3 N (σ' z) (σ z) = 0 from
          Matrix.diagonal_apply_ne _ hz]]
      ring
    · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy N hzx hzy hz

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}` with
`σ' ≠ σ`, the spinSDot matrix element of any pair `(x', y')` with
`x' ≠ y'` and `x'` outside `{x, y}` vanishes. (The non-zero
off-diagonal entries of `Ŝ_x · Ŝ_y` are confined to the supporting
two-site set.) -/
theorem spinSDot_apply_eq_zero_of_x_outside_pair
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    {x' y' : Λ} (hxy' : x' ≠ y')
    (hxx' : x' ≠ x) (hyx' : x' ≠ y) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hxd : σ' x = σ x
  · by_cases hyd : σ' y = σ y
    · exfalso
      apply hne
      funext k
      by_cases hkx : k = x
      · subst hkx; exact hxd
      · by_cases hky : k = y
        · subst hky; exact hyd
        · exact h k hkx hky
    · by_cases hyy' : y = y'
      · have hagree : ∀ k, k ≠ y' → σ' k = σ k := fun k hk => by
          subst hyy'
          by_cases hkx : k = x
          · subst hkx; exact hxd
          · exact h k hkx hk
        exact spinSDot_apply_eq_zero_of_one_site_diff hxy' N hagree
          (hyy' ▸ hyd)
      · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
          (Ne.symm hyx') hyy' hyd
  · by_cases hxy2 : x = y'
    · by_cases hyd : σ' y = σ y
      · have hagree : ∀ k, k ≠ y' → σ' k = σ k := fun k hk => by
          subst hxy2
          by_cases hky : k = y
          · subst hky; exact hyd
          · exact h k hk hky
        exact spinSDot_apply_eq_zero_of_one_site_diff hxy' N hagree
          (hxy2 ▸ hxd)
      · have hyy' : y ≠ y' := fun heq => hxy.symm (heq.trans hxy2.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
          (Ne.symm hyx') hyy' hyd
    · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
        (Ne.symm hxx') (Ne.symm fun heq => hxy2 heq.symm) hxd

/-- Symmetric: `y'` outside `{x, y}` also vanishes (using `spinSDot_comm`). -/
theorem spinSDot_apply_eq_zero_of_y_outside_pair
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    {x' y' : Λ} (hxy' : x' ≠ y')
    (hxy'' : y' ≠ x) (hyy' : y' ≠ y) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [show (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ =
      (spinSDot y' x' N : ManyBodyOpS Λ N) σ' σ from by
    rw [spinSDot_comm]]
  exact spinSDot_apply_eq_zero_of_x_outside_pair hxy N hne h
    (Ne.symm hxy') hxy'' hyy'

/-- For `x' ≠ y'`, if there are three pairwise-distinct sites
`z₁, z₂, z₃` where `σ', σ` differ, the spinSDot matrix element
vanishes (pigeonhole: at least one of the three is outside `{x', y'}`). -/
theorem spinSDot_apply_eq_zero_of_three_diff
    {x' y' : Λ} (hxy' : x' ≠ y') (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z₁ z₂ z₃ : Λ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  -- Find a zᵢ outside {x', y'}; pigeonhole on the 2-element set.
  by_cases h1x : z₁ = x'
  · by_cases h1y : z₁ = y'
    · -- z₁ = x' and z₁ = y' contradicts hxy'.
      exact (hxy' (h1x.symm.trans h1y)).elim
    · -- z₁ = x' but z₁ ≠ y'. So if z₂ = x', then z₂ = z₁, contradicting h12.
      -- So z₂ ≠ x'. Now case on z₂ = y'.
      have h2x : z₂ ≠ x' := fun heq => h12 (h1x.trans heq.symm)
      by_cases h2y : z₂ = y'
      · -- z₁ = x' and z₂ = y'. Now z₃ ∉ {x', y'} (else z₃ = z₁ or z₂).
        have h3x : z₃ ≠ x' := fun heq => h13 (h1x.trans heq.symm)
        have h3y : z₃ ≠ y' := fun heq => h23 (h2y.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h3x h3y hz3
      · -- z₂ ∉ {x', y'}.
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h2x h2y hz2
  · by_cases h1y : z₁ = y'
    · -- z₁ = y'.
      have h2y : z₂ ≠ y' := fun heq => h12 (h1y.trans heq.symm)
      by_cases h2x : z₂ = x'
      · -- z₁ = y' and z₂ = x'. z₃ ∉ {x', y'}.
        have h3x : z₃ ≠ x' := fun heq => h23 (h2x.trans heq.symm)
        have h3y : z₃ ≠ y' := fun heq => h13 (h1y.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h3x h3y hz3
      · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h2x h2y hz2
    · -- z₁ ∉ {x', y'}.
      exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h1x h1y hz1

/-- **Combined off-pair vanishing**: for `x ≠ y`, `σ', σ` agreeing
off `{x, y}` with `σ' ≠ σ`, and `(x', y')` not equal to `(x, y)` or
`(y, x)`, the spinSDot matrix element vanishes.

Cases: `x' = y'` gives the same-site Casimir vanishing on `σ' ≠ σ`;
otherwise at least one of `x', y'` is outside `{x, y}` (since
`{x', y'} ⊆ {x, y}` and `x' ≠ y'` would force `(x', y') ∈
{(x, y), (y, x)}`), so the corresponding outside-pair lemma applies. -/
theorem spinSDot_apply_eq_zero_of_pair_not_xy_or_yx
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (x' y' : Λ)
    (hpair : ¬ ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x))) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hxy' : x' = y'
  · subst hxy'
    have ⟨z, hz⟩ : ∃ z, σ' z ≠ σ z := Function.ne_iff.mp hne
    exact spinSDot_self_apply_eq_zero_of_diff_at x' N hz
  · -- x' ≠ y'. At least one of x', y' is outside {x, y} (else (x',y') would
    -- be (x,y) or (y,x), which is excluded).
    by_cases hxx' : x' = x
    · -- x' = x; then y' ≠ y (else hpair would be Or.inl). And y' ≠ x' = x (hxy').
      have hyy : y' ≠ y := fun heq => hpair (Or.inl ⟨hxx', heq⟩)
      have hyx : y' ≠ x := fun heq => hxy' (hxx'.trans heq.symm)
      exact spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hxy' hyx hyy
    · by_cases hxy2 : x' = y
      · -- x' = y; then y' ≠ x (else hpair would be Or.inr). And y' ≠ y (hxy').
        have hyx : y' ≠ x := fun heq => hpair (Or.inr ⟨hxy2, heq⟩)
        have hyy : y' ≠ y := fun heq => hxy' (hxy2.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hxy' hyx hyy
      · -- x' ∉ {x, y}; use x_outside.
        exact spinSDot_apply_eq_zero_of_x_outside_pair hxy N hne h hxy' hxx' hxy2

/-- **spinSDot vanishing on non-`±1` differences at `x`**: for `x ≠ y`
and configurations `σ', σ` agreeing off `{x, y}` such that `σ', σ`
differ at `x` by an amount other than `±1` (i.e., neither raising nor
lowering by one step), the matrix element vanishes.

The `S^+_x ⊗ S^-_y` term vanishes (since `S^+(σ' x, σ x) = 0` requires
`(σ' x).val + 1 = (σ x).val`); the `S^-_x ⊗ S^+_y` term vanishes
(since `S^-(σ' x, σ x) = 0` requires `(σ x).val + 1 = (σ' x).val`);
the `S^3_x ⊗ S^3_y` term vanishes (since `σ' x ≠ σ x` forces
`S^3(σ' x, σ x) = 0`). -/
theorem spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hne : σ' x ≠ σ x)
    (hp : (σ' x).val + 1 ≠ (σ x).val)
    (hm : (σ x).val + 1 ≠ (σ' x).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hne]
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpPlus_apply_other N hp]
  rw [spinSOpMinus_apply_other N hm]
  ring

/-- Symmetric: spinSDot vanishes when the difference at `y` is not
`±1`. -/
theorem spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hne : σ' y ≠ σ y)
    (hp : (σ' y).val + 1 ≠ (σ y).val)
    (hm : (σ y).val + 1 ≠ (σ' y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_y hxy N h hne]
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpMinus_apply_other N hm]
  rw [spinSOpPlus_apply_other N hp]
  ring


end LatticeSystem.Quantum
