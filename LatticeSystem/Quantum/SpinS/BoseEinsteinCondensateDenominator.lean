import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateMoment
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): tower denominator lower bound and
non-vanishing (PR-4)

This file supplies the **denominator side** of the Bose–Einstein-condensation tower discharge
(`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)): a geometric lower bound on the squared tower
amplitude `⟨Φ, (ô^∓)^{|M|} (ô^±)^{|M|} Φ⟩ ≥ ½ (2 q₀)^{|M|} m₀`, and the resulting non-vanishing of
the tower state `Γ_M = (Ô_L^{sgn M})^{|M|} Φ ≠ 0` (the first conclusion of `IsBECTowerConstants`).

The mechanism is identical to the Anderson-tower Theorem 4.6 denominator:

* the renormalized-product estimate `tower_denominator_lower_bound(_lower)`
  (`AndersonTowerEnergyBoundR1.lean`) gives `½ P_M ≤ ⟨Φ, (ô^∓)^M (ô^±)^M Φ⟩` under the range
  condition `3 N M² ≤ 2 q₀ V`.  It needs **only** the `Ŝ_tot^{(3)} = 0` half-filling hypothesis
  (`hsing`), *not* the full `SU(2)` singlet — so it applies verbatim to the `μ = 0`
  chemical-potential XY ground state, which lives in the `Ŝ_tot^{(3)} = 0` sector (half filling,
  Theorem 2.4);
* the moment geometric lower bound `phatMoment_ge_of_lro`
  (`AndersonTowerEnergyBoundPhat.lean`) gives `(2 q₀)^M m₀ ≤ P_M`, fed by the `U(1)`-planar base
  entry `phatMoment_one_ge_of_planar_lro` (PR-2) rather than the `SU(2)` isotropy base.

Combining the two yields `½ (2 q₀)^M m₀ ≤ ⟨Φ, (ô^∓)^M (ô^±)^M Φ⟩`, whence the tower state is nonzero
whenever `q₀ > 0` and `m₀ > 0`.  These are consumed by the later assembly PR (the Rayleigh bound of
eq. (5.3.4) divides the numerator by this denominator; the non-vanishing supplies the first conjunct
of `IsBECTowerConstants`).

The chemical-potential Hamiltonian is `μ = 0` here (half filling), so the denominator bound needs
only the half-filling `Ŝ_tot^{(3)} = 0` sector; the general-`μ` case stays the documented axiom
`tasaki_5_2_bec_tower`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eqs. (5.2.5)/(5.3.3)/(5.3.4), pp. 139–141 (Koma–Tasaki [21]); the
denominator mechanism is eq. (4.2.37)/(4.2.67), pp. 105–106.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Raising-tower denominator geometric lower bound** (Tasaki §5.3, eq. (4.2.37) applied to the
planar tower).  Under the half-filling hypothesis `hsing : Ŝ_tot^{(3)} Φ = 0`, the reduced planar
long-range-order base entry `2 q₀ m₀ ≤ m₁`, and the range condition `3 N M² ≤ 2 q₀ V`, the squared
per-volume raising-tower amplitude obeys
`½ (2 q₀)^M m₀ ≤ ⟨Φ, (ô⁻)^M (ô⁺)^M Φ⟩ = ‖(ô⁺)^M Φ‖²`.  Combines the balanced-word denominator bound
`tower_denominator_lower_bound` (which needs only `Ŝ_tot^{(3)} = 0`, not the full singlet) with the
moment geometric lower bound `phatMoment_ge_of_lro`.  This is the denominator feeding the raising
branch of the Rayleigh bound of eq. (5.3.4). -/
theorem becTowerDenominator_geom_lower_raising (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    {M : ℕ} (hcond : 3 * (N : ℝ) * (M : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    (1 / 2) * (2 * q₀) ^ M * phatMoment d L N Φ 0
      ≤ (star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ M
          * staggeredOrderDensityOpS d L N true ^ M).mulVec Φ).re := by
  have hden := tower_denominator_lower_bound d L N hN Φ hsing hm0 hlro hcond
  have hgeom : (2 * q₀) ^ M * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ M := by
    cases M with
    | zero => simp
    | succ k => exact phatMoment_ge_of_lro d L N Φ hq₀ hm0 hlro k
  linarith

/-- **Lowering-tower denominator geometric lower bound** (mirror of
`becTowerDenominator_geom_lower_raising` for the lowering branch).  Under the same hypotheses the
squared per-volume lowering-tower amplitude obeys
`½ (2 q₀)^M m₀ ≤ ⟨Φ, (ô⁺)^M (ô⁻)^M Φ⟩ = ‖(ô⁻)^M Φ‖²`.  Combines the lowering balanced-word
bound `tower_denominator_lower_bound_lower` with `phatMoment_ge_of_lro`; this is the denominator
feeding the lowering branch of the Rayleigh bound of eq. (5.3.4). -/
theorem becTowerDenominator_geom_lower_lowering (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    {M : ℕ} (hcond : 3 * (N : ℝ) * (M : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    (1 / 2) * (2 * q₀) ^ M * phatMoment d L N Φ 0
      ≤ (star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N true ^ M
          * staggeredOrderDensityOpS d L N false ^ M).mulVec Φ).re := by
  have hden := tower_denominator_lower_bound_lower d L N hN Φ hsing hm0 hlro hcond
  have hgeom : (2 * q₀) ^ M * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ M := by
    cases M with
    | zero => simp
    | succ k => exact phatMoment_ge_of_lro d L N Φ hq₀ hm0 hlro k
  linarith

/-- **Non-vanishing of the BEC tower state** (Tasaki §5.3, well-definedness of `Γ_M`, first conjunct
of `IsBECTowerConstants`).  For the `μ = 0` chemical-potential XY ground state `Φ` (half filling,
`hsing : Ŝ_tot^{(3)} Φ = 0`) with `q₀ > 0`, `m₀ > 0`, the two XY-plane ODLRO hypotheses
(`α = 1, 2`), and `M` within the tower range (`3 (M.natAbs)² ≤ 2 q₀ V`, the `N = 1` spin-`1/2`
form), the tower state `Γ_M = (Ô_L^{sgn M})^{|M|} Φ` is nonzero.  The squared tower amplitude is
`V^{2|M|}` times the per-volume denominator, which the geometric lower bound
`becTowerDenominator_geom_lower_(raising/lowering)` keeps `≥ ½ (2 q₀)^{|M|} m₀ > 0`; the scalar
`V^{|M|} ≠ 0` then transfers non-vanishing to `Γ_M`.  The planar base entry `2 q₀ m₀ ≤ m₁` is
supplied by the `U(1)` PR-2 lemma `phatMoment_one_ge_of_planar_lro`. -/
theorem becTowerState_ne_zero_of_planar_lro (d L : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hm0 : 0 < phatMoment d L 1 Φ 0)
    (hlro : ∀ α : Fin 3, α ≠ 2 →
      q₀ ≤ expectationRatioRe
        ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2)
    (M : ℤ) (hcond : 3 * (1 : ℝ) * (M.natAbs : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    towerState (torusParitySublattice d L) 1 M Φ ≠ 0 := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLcne : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))
  -- reduce the two planar ODLRO hypotheses to the moment base entry `2 q₀ m₀ ≤ m₁`
  have hbase : 2 * q₀ * phatMoment d L 1 Φ 0 ≤ phatMoment d L 1 Φ 1 := by
    have h := phatMoment_one_ge_of_planar_lro d L 1 Φ q₀ (by rw [← phatMoment_zero]; exact hm0)
      hLpos hlro
    rwa [phatMoment_zero]
  -- `0 < ½ (2 q₀)^{|M|} m₀`
  have hpospref : (0 : ℝ) < (1 / 2) * (2 * q₀) ^ M.natAbs * phatMoment d L 1 Φ 0 := by
    have : (0 : ℝ) < (2 * q₀) ^ M.natAbs := pow_pos (by positivity) _
    positivity
  by_cases hM : 0 ≤ M
  · -- raising branch: `Γ_M = V^{|M|} • (ô⁺)^{|M|} Φ`
    set m := M.natAbs with hmdef
    have hMm : M = (m : ℤ) := (Int.natAbs_of_nonneg hM).symm
    have hden := becTowerDenominator_geom_lower_raising d L 1 (le_refl 1) Φ hsing hq₀.le hm0
      hbase (M := m) (by exact_mod_cast hcond)
    -- the per-volume denominator is the squared norm of `(ô⁺)^m Φ`
    have hnorm : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L 1 false ^ m
          * staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ
        = star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ)
            ⬝ᵥ (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ := by
      rw [← Matrix.mulVec_mulVec, orderDensityFalse_pow_eq_conjTranspose,
        star_dotProduct_mulVec_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have hpos : 0 < (star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ)
        ⬝ᵥ (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ).re := by
      rw [← hnorm]; linarith
    have hunz : (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ ≠ 0 := by
      intro hu
      simp only [hu, star_zero, zero_dotProduct, Complex.zero_re, lt_self_iff_false] at hpos
    rw [hMm, towerState_pos_eq_smul]
    exact smul_ne_zero (pow_ne_zero m hLcne) hunz
  · -- lowering branch: `Γ_M = V^{|M|} • (ô⁻)^{|M|} Φ`, `|M| ≥ 1`
    set m := M.natAbs with hmdef
    have hm1 : 1 ≤ m := by omega
    have hMm : M = -(m : ℤ) := by omega
    have hden := becTowerDenominator_geom_lower_lowering d L 1 (le_refl 1) Φ hsing hq₀.le hm0
      hbase (M := m) (by exact_mod_cast hcond)
    have hnorm : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L 1 true ^ m
          * staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ
        = star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ)
            ⬝ᵥ (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ := by
      have htrue : staggeredOrderDensityOpS d L 1 true ^ m
          = Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 false ^ m) := by
        rw [orderDensityFalse_pow_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.mulVec_mulVec, htrue, star_dotProduct_mulVec_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    have hpos : 0 < (star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ)
        ⬝ᵥ (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ).re := by
      rw [← hnorm]; linarith
    have hunz : (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ ≠ 0 := by
      intro hu
      simp only [hu, star_zero, zero_dotProduct, Complex.zero_re, lt_self_iff_false] at hpos
    rw [hMm, towerState_neg_eq_smul d L 1 m hm1]
    exact smul_ne_zero (pow_ne_zero m hLcne) hunz

end LatticeSystem.Quantum
