import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.SingleSiteZExpectation

/-!
# `Ŝ_x · Ŝ_y · |σ_⊤⟩ = (N²/4) · |σ_⊤⟩` for distinct sites

For distinct sites `x ≠ y` on the saturated-ferromagnet state
`|σ_⊤⟩`, the two-site dot product `Ŝ_x · Ŝ_y` acts as the scalar
`N²/4 = S²`:

  `Ŝ_x · Ŝ_y · |σ_⊤⟩ = (N²/4) · |σ_⊤⟩` for `x ≠ y`.

Proof: use `spinSDot_eq_plus_minus`
(`Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^{(3)} Ŝ_y^{(3)}`).
- Both `+/−` terms vanish on `|σ_⊤⟩`: `Ŝ_y^+ |σ_⊤⟩ = 0`
  (highest weight at `y`); `Ŝ_x^+` applied after `Ŝ_y^-` lands on
  one-flipped at `y` where `σ_x = 0` is still highest weight, so
  `Ŝ_x^+ |...⟩ = 0`.
- The `(3)(3)` term gives `(N/2)·(N/2) · |σ_⊤⟩ = (N²/4) · |σ_⊤⟩`.

Symmetric for the all-down state.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `Ŝ_x · Ŝ_y · |σ_⊤⟩ = (N²/4) · |σ_⊤⟩` for `x ≠ y`. -/
theorem spinSDot_mulVec_allAlignedStateS_zero_of_ne
    {x y : V} (hxy : x ≠ y) :
    (spinSDot x y N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((N : ℂ) * (N : ℂ) / 4) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  rw [spinSDot_eq_plus_minus]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec]
  -- Goal: (1/2) • (((onSiteS x Ŝ^+) * (onSiteS y Ŝ^-)).mulVec |⊤⟩
  --              + ((onSiteS x Ŝ^-) * (onSiteS y Ŝ^+)).mulVec |⊤⟩)
  --     + ((onSiteS x Ŝ^(3)) * (onSiteS y Ŝ^(3))).mulVec |⊤⟩
  --     = (N²/4) • |⊤⟩.
  -- Step 1: ((onSiteS x Ŝ^-) * (onSiteS y Ŝ^+)).mulVec |⊤⟩ = 0
  -- (since (onSiteS y Ŝ^+) |⊤⟩ = 0).
  have h_minus_plus : ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpPlus N)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [onSiteS_spinSOpPlus_mulVec_allAlignedStateS_zero]
    rw [Matrix.mulVec_zero]
  -- Step 2: ((onSiteS x Ŝ^+) * (onSiteS y Ŝ^-)).mulVec |⊤⟩ = 0
  -- (after Ŝ^-_y, σ_x = 0 still, so Ŝ^+_x |0⟩_x = 0).
  have h_plus_minus : ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) *
      onSiteS y (spinSOpMinus N)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) = 0 := by
    -- Apply Ŝ^-_y at |⊤⟩, then Ŝ^+_x. At y ≠ x, the result has σ_x = 0 still.
    rw [← Matrix.mulVec_mulVec]
    -- Show the inner result has σ_x = 0 at site x, so Ŝ^+_x · ... = 0 entry-wise.
    -- Cleanest: evaluate at any τ and show every entry vanishes.
    funext τ
    simp only [Pi.zero_apply]
    rw [Matrix.mulVec, dotProduct]
    -- ∑_ρ (onSiteS x Ŝ^+) τ ρ * ((onSiteS y Ŝ^-).mulVec |⊤⟩) ρ.
    -- Use that (onSiteS x Ŝ^+) τ ρ ≠ 0 only when τ, ρ agree off x and (Ŝ^+) (τ x) (ρ x) ≠ 0,
    -- which requires τ.x + 1 = ρ.x.
    -- And ((onSiteS y Ŝ^-).mulVec |⊤⟩) ρ ≠ 0 only when ρ matches the y-flipped config.
    -- The y-flipped config has σ_x = 0 (since y ≠ x), so ρ x = 0.
    -- Then (Ŝ^+) (τ x) (0) = 0 unless τ x + 1 = 0, impossible.
    apply Finset.sum_eq_zero
    intros ρ _
    -- Check (onSiteS x Ŝ^+) τ ρ * ... = 0.
    by_cases h_off : ∀ k, k ≠ x → τ k = ρ k
    · -- On-site agreement: (onSiteS x Ŝ^+) τ ρ = (Ŝ^+) (τ x) (ρ x).
      rw [onSiteS_apply_of_off_site_agree x _ h_off]
      -- We need to show (Ŝ^+) (τ x) (ρ x) * (...).mulVec |⊤⟩ ρ = 0.
      -- Compute (onSiteS y Ŝ^-).mulVec |⊤⟩ ρ.
      have h_inner : ((onSiteS y (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1)))) ρ =
          (onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) ρ
            (allAlignedConfigS V N 0) := by
        rw [Matrix.mulVec, dotProduct]
        unfold allAlignedStateS
        rw [Finset.sum_eq_single (allAlignedConfigS V N 0)]
        · rw [basisVecS_self, mul_one]
        · intros σ _ hσne
          rw [basisVecS_of_ne hσne, mul_zero]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      rw [h_inner]
      -- Now we have spinSOpPlus N (τ x) (ρ x) * onSiteS y Ŝ^- ρ σ_⊤.
      -- For the second factor to be ≠ 0, ρ must agree with σ_⊤ off site y, and
      -- (Ŝ^-) (ρ y) (0) ≠ 0 requires ρ y = 1 (lowering 0 → 1).
      by_cases h_off_y : ∀ k, k ≠ y → ρ k = allAlignedConfigS V N 0 k
      · rw [onSiteS_apply_of_off_site_agree y _ h_off_y]
        -- ρ x = allAlignedConfigS V N 0 x = 0 (since ρ agrees with const 0 off y).
        have hρ_x : ρ x = allAlignedConfigS V N 0 x :=
          h_off_y x hxy
        have hρ_x' : ρ x = (0 : Fin (N + 1)) := hρ_x
        rw [hρ_x']
        -- (Ŝ^+) (τ x) 0 = 0 since (τ x).val + 1 ≠ 0.
        have h_zero : (spinSOpPlus N) (τ x) (0 : Fin (N + 1)) = 0 := by
          apply spinSOpPlus_apply_other
          show (τ x).val + 1 ≠ ((0 : Fin (N + 1)).val)
          simp
        rw [h_zero, zero_mul]
      · -- Off y agreement fails: (onSiteS y Ŝ^-) ρ σ_⊤ = 0.
        rw [onSiteS_apply_eq_zero_of_off_site_diff y _ h_off_y]
        rw [mul_zero]
    · -- Off x agreement fails: (onSiteS x Ŝ^+) τ ρ = 0.
      rw [onSiteS_apply_eq_zero_of_off_site_diff x _ h_off]
      rw [zero_mul]
  -- Step 3: (Ŝ^(3)_x · Ŝ^(3)_y) · |⊤⟩ = (N/2)² · |⊤⟩.
  have h_z_z : ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
      onSiteS y (spinSOp3 N)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2)) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
    rw [← Matrix.mulVec_mulVec]
    rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
    rw [Matrix.mulVec_smul]
    rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
    rw [smul_smul]
    rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
    push_cast; ring_nf
  rw [h_plus_minus, h_minus_plus, h_z_z]
  rw [add_zero, smul_zero, zero_add]
  congr 1
  ring

end LatticeSystem.Quantum
