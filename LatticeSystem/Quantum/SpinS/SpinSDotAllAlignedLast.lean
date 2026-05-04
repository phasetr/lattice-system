import LatticeSystem.Quantum.SpinS.SpinSDotAllAlignedZero

/-!
# `Ŝ_x · Ŝ_y · |σ_⊥⟩ = (N²/4) · |σ_⊥⟩` for distinct sites

Symmetric raising-side counterpart of PR #939: for `x ≠ y` on the
saturated-ferromagnet all-down state `|σ_⊥⟩`,

  `Ŝ_x · Ŝ_y · |σ_⊥⟩ = (N²/4) · |σ_⊥⟩`.

Proof structure mirrors PR #939 with `Ŝ^+ ↔ Ŝ^-`, `0 ↔ N` swapped:
- The `+,-` and `-,+` cross terms vanish via lowering-side
  highest-weight analogue (`Ŝ^-_y · |σ_⊥⟩ = 0`).
- The `(3)(3)` term gives `(-N/2)·(-N/2) · |σ_⊥⟩ = (N²/4) · |σ_⊥⟩`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `Ŝ_x · Ŝ_y · |σ_⊥⟩ = (N²/4) · |σ_⊥⟩` for `x ≠ y`. -/
theorem spinSDot_mulVec_allAlignedStateS_last_of_ne
    {x y : V} (hxy : x ≠ y) :
    (spinSDot x y N).mulVec
        (allAlignedStateS V N (Fin.last N)) =
      ((N : ℂ) * (N : ℂ) / 4) •
        allAlignedStateS V N (Fin.last N) := by
  rw [spinSDot_eq_plus_minus]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec]
  -- Step 1: ((onSiteS x Ŝ^+) * (onSiteS y Ŝ^-)).mulVec |⊥⟩ = 0
  -- since Ŝ^-_y · |⊥⟩ = 0 (lowest weight).
  have h_plus_minus : ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpMinus N)).mulVec
        (allAlignedStateS V N (Fin.last N)) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [onSiteS_spinSOpMinus_mulVec_allAlignedStateS_last]
    rw [Matrix.mulVec_zero]
  -- Step 2: ((onSiteS x Ŝ^-) * (onSiteS y Ŝ^+)).mulVec |⊥⟩ = 0
  -- (after Ŝ^+_y · |⊥⟩ = (some N) · |y-raised⟩, σ_x = N still, Ŝ^-_x |N⟩ = 0).
  have h_minus_plus : ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpPlus N)).mulVec
        (allAlignedStateS V N (Fin.last N)) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    funext τ
    simp only [Pi.zero_apply]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intros ρ _
    by_cases h_off : ∀ k, k ≠ x → τ k = ρ k
    · rw [onSiteS_apply_of_off_site_agree x _ h_off]
      have h_inner : ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (allAlignedStateS V N (Fin.last N))) ρ =
          (onSiteS y (spinSOpPlus N) : ManyBodyOpS V N) ρ
            (allAlignedConfigS V N (Fin.last N)) := by
        rw [Matrix.mulVec, dotProduct]
        unfold allAlignedStateS
        rw [Finset.sum_eq_single (allAlignedConfigS V N (Fin.last N))]
        · rw [basisVecS_self, mul_one]
        · intros σ _ hσne
          rw [basisVecS_of_ne hσne, mul_zero]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      rw [h_inner]
      by_cases h_off_y : ∀ k, k ≠ y → ρ k = allAlignedConfigS V N (Fin.last N) k
      · rw [onSiteS_apply_of_off_site_agree y _ h_off_y]
        have hρ_x : ρ x = allAlignedConfigS V N (Fin.last N) x :=
          h_off_y x hxy
        have hρ_x' : ρ x = (Fin.last N : Fin (N + 1)) := hρ_x
        rw [hρ_x']
        -- (Ŝ^-) (τ x) (Fin.last N) = 0 since (Fin.last N).val + 1 = N + 1 ≠ (τ x).val.
        have h_zero : (spinSOpMinus N) (τ x) (Fin.last N : Fin (N + 1)) = 0 := by
          apply spinSOpMinus_apply_other
          show (Fin.last N).val + 1 ≠ (τ x).val
          have hτ_lt : (τ x).val < N + 1 := (τ x).isLt
          simp [Fin.last]; omega
        rw [h_zero, zero_mul]
      · rw [onSiteS_apply_eq_zero_of_off_site_diff y _ h_off_y]
        rw [mul_zero]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ h_off]
      rw [zero_mul]
  -- Step 3: (Ŝ^(3)_x · Ŝ^(3)_y) · |⊥⟩ = (-N/2)² · |⊥⟩.
  have h_z_z : ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
      onSiteS y (spinSOp3 N)).mulVec
        (allAlignedStateS V N (Fin.last N)) =
      (((N : ℂ) / 2 - (Fin.last N).val) *
        ((N : ℂ) / 2 - (Fin.last N).val)) •
        allAlignedStateS V N (Fin.last N) := by
    rw [← Matrix.mulVec_mulVec]
    rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
    rw [Matrix.mulVec_smul]
    rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
    rw [smul_smul]
  rw [h_plus_minus, h_minus_plus, h_z_z]
  rw [add_zero, smul_zero, zero_add]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  congr 1
  ring

/-! ## Generalisation: only `σ x = σ y = Fin.last N` needed -/

/-- `Ŝ_x · Ŝ_y · basisVecS σ = (N²/4) · basisVecS σ` whenever `x ≠ y`,
`σ x = Fin.last N`, and `σ y = Fin.last N`. Lowest-weight counterpart
of `spinSDot_mulVec_basisVecS_zero_of_ne` (PR #1064): generalises
`spinSDot_mulVec_allAlignedStateS_last_of_ne` to allow arbitrary σ
outside of `{x, y}`. -/
theorem spinSDot_mulVec_basisVecS_last_of_ne
    {x y : V} (hxy : x ≠ y) (σ : V → Fin (N + 1))
    (hx : σ x = Fin.last N) (hy : σ y = Fin.last N) :
    (spinSDot x y N).mulVec (basisVecS σ) =
      ((N : ℂ) * (N : ℂ) / 4) • basisVecS σ := by
  rw [spinSDot_eq_plus_minus]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec]
  -- Step 1: Ŝ^-_y annihilates basisVecS σ when σ y = Fin.last N.
  have h_y_minus : (onSiteS y (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (basisVecS σ) = 0 := by
    funext τ
    rw [onSiteS_mulVec_basisVecS_apply]
    change (onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) τ σ = 0
    by_cases h_off : ∀ k, k ≠ y → τ k = σ k
    · rw [onSiteS_apply_of_off_site_agree y _ h_off]
      rw [hy]
      apply spinSOpMinus_apply_other
      show ((Fin.last N).val : ℕ) + 1 ≠ (τ y).val
      have hτ_lt : (τ y).val < N + 1 := (τ y).isLt
      simp [Fin.last]; omega
    · exact onSiteS_apply_eq_zero_of_off_site_diff y _ h_off
  have h_plus_minus : ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpMinus N)).mulVec (basisVecS σ) = 0 := by
    rw [← Matrix.mulVec_mulVec, h_y_minus, Matrix.mulVec_zero]
  -- Step 2: Ŝ^-_x annihilates the Ŝ^+_y-image of basisVecS σ.
  have h_minus_plus : ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpPlus N)).mulVec (basisVecS σ) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    funext τ
    simp only [Pi.zero_apply]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intros ρ _
    by_cases h_off : ∀ k, k ≠ x → τ k = ρ k
    · rw [onSiteS_apply_of_off_site_agree x _ h_off]
      have h_inner : ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (basisVecS σ)) ρ =
          (onSiteS y (spinSOpPlus N) : ManyBodyOpS V N) ρ σ :=
        onSiteS_mulVec_basisVecS_apply y _ σ ρ
      rw [h_inner]
      by_cases h_off_y : ∀ k, k ≠ y → ρ k = σ k
      · rw [onSiteS_apply_of_off_site_agree y _ h_off_y]
        have hρ_x : ρ x = σ x := h_off_y x hxy
        rw [hρ_x, hx]
        have h_zero : (spinSOpMinus N) (τ x) (Fin.last N : Fin (N + 1)) = 0 := by
          apply spinSOpMinus_apply_other
          show ((Fin.last N).val : ℕ) + 1 ≠ (τ x).val
          have hτ_lt : (τ x).val < N + 1 := (τ x).isLt
          simp [Fin.last]; omega
        rw [h_zero, zero_mul]
      · rw [onSiteS_apply_eq_zero_of_off_site_diff y _ h_off_y]
        rw [mul_zero]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ h_off]
      rw [zero_mul]
  -- Step 3: Diagonal Ŝ^(3) Ŝ^(3) gives (-N/2)² = N²/4.
  have h_z_z : ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
      onSiteS y (spinSOp3 N)).mulVec (basisVecS σ) =
      (((N : ℂ) / 2 - (σ y).val) * ((N : ℂ) / 2 - (σ x).val)) •
        basisVecS σ := by
    rw [← Matrix.mulVec_mulVec]
    rw [onSiteS_spinSOp3_mulVec_basisVecS]
    rw [Matrix.mulVec_smul]
    rw [onSiteS_spinSOp3_mulVec_basisVecS]
    rw [smul_smul]
  rw [h_plus_minus, h_minus_plus, h_z_z]
  rw [add_zero, smul_zero, zero_add]
  rw [hx, hy]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  congr 1
  ring

end LatticeSystem.Quantum
