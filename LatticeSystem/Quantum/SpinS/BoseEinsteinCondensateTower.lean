import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateXYNumerator
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateDenominator

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): half-filling tower-energy assembly (PR-5)

This file assembles the **half-filling (`μ = 0`) tower-energy bound** of the
Bose–Einstein-condensation tower (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4), footnote 8,
p. 141) and constructs the constants of the half-filling predicate
`IsBECTowerConstantsHalfFilling` (defined in `BoseEinsteinCondensate.lean`).

At half filling the chemical-potential Hamiltonian collapses to `Ĥ_0 = 2 Ĥ_XY` (the `−μ Ŝ_tot^{(3)}`
term of eq. (5.3.2) vanishes at `μ = 0`), so the variational double commutator is the pure XY
numerator `xy_tower_numerator_bound` (PR-4b) — there is no residual first-order `μ`-term.  The
assembly is the BEC counterpart of the Anderson-tower Theorem 4.6 trial-energy bound:

* the general variational gap `variational_gap_le_double_commutator` bounds the trial-state energy
  gap by the double commutator of `Aᴴ = (ô^∓)^m` with `[Ĥ_0, A]`, `A = (ô^±)^m`;
* the numerator is `xy_tower_numerator_bound` (`4` copies of the `O(m²/V)` moment-factor shape),
  whose moment factors are converted to the `p̂`-moment `P_m` by `momentFactor_twoM_sub_two_le` /
  `momentFactor_twoM_sub_three_le` with the XY-plane recursion (`phatMoment_succ_ratio` fed by the
  planar base `phatMoment_one_ge_of_planar_lro`, PR-2);
* the denominator lower bound `½ P_m ≤ ‖(ô^±)^m Φ‖²` (`tower_denominator_lower_bound(_lower)`, which
  needs only the `Ŝ_tot^{(3)} = 0` half-filling sector) cancels the `P_m`, leaving the Rayleigh
  bound `≤ E₀ + 8 · towerEnergyCoeff` (the factor `4` of the XY split doubles the Heisenberg `2`).

The trial bound is `O(m²/V)` (`towerEnergyCoeff_le`); rounding `m² ≤ |M|³` for `|M| ≥ 1` gives the
faithful **cubic** increment `C₂ |M|³ / L^d` of eq. (5.3.4) (footnote 8: the cubic bound is
Tasaki's deliberately weakened form).  The non-vanishing conjunct is
`becTowerState_ne_zero_of_planar_lro` (PR-4).  The general-`μ` bound stays the documented axiom
`tasaki_5_2_bec_tower`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eq. (5.3.4), footnote 8, pp. 140–141 (Koma–Tasaki [21]); the
Anderson-tower engine is §4.2.2 Theorem 4.6, eqs. (4.2.31)/(4.2.37), pp. 105–106.  The
pre-implementation
mathematical derivation is `.self-local/docs/math-thm52-bec-tower.md` §4.3 and the arc design note
`.self-local/reports/design-thm52-final-arc.md` §PR-5.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **The half-filling chemical-potential Hamiltonian is `2 Ĥ_XY`.**  At `μ = 0` the
`−μ Ŝ_tot^{(3)}` term of `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` (eq. (5.3.2)) vanishes, so `Ĥ_0 = 2 Ĥ_XY`.
This is the
collapse that lets the pure-XY numerator `xy_tower_numerator_bound` drive the half-filling assembly
without a residual first-order `μ`-term. -/
theorem xyChemicalPotentialHamiltonianS_zero (d L : ℕ) [NeZero L] :
    xyChemicalPotentialHamiltonianS d L 0 = (2 : ℂ) • xyHamiltonianS d L := by
  simp [xyChemicalPotentialHamiltonianS]

set_option maxHeartbeats 1600000 in -- large variational-gap + numerator moment-factor rewrite
/-- **Half-filling raising-tower Rayleigh bound** (Tasaki §5.3, eq. (5.3.4) at `μ = 0`, raising
branch).  For the half-filling XY ground state `Φ` (`Ŝ_tot^{(3)} Φ = 0`, `hsing`) with the two
XY-plane ODLRO bounds, the raising tower state `Γ_m = (Ô_L^+)^m Φ` (`m ≥ 1`) obeys the quadratic
Rayleigh bound `⟨Γ_m, Ĥ_0 Γ_m⟩ / ⟨Γ_m, Γ_m⟩ ≤ E₀ + 8 · towerEnergyCoeff`.  The variational gap
(`variational_gap_le_double_commutator`) is bounded by the pure-XY numerator
`xy_tower_numerator_bound` (`4` moment-factor copies), whose `p̂`-moments are supplied by the
XY-plane recursion; the denominator `½ P_m ≤ ‖(ô⁺)^m Φ‖²` (`tower_denominator_lower_bound`) cancels
the `P_m`.  The factor `8` is `2 · 4` (the `4` of the XY = Heisenberg − ZZ split). -/
theorem becTowerState_pos_rayleigh_bound_halfFilling (d L m : ℕ) [NeZero L] (hL : 2 ≤ L)
    (hm : 1 ≤ m) (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ)
    (hev : (xyChemicalPotentialHamiltonianS d L 0).mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin 2) → ℂ), Ψ ≠ 0 →
       (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    (hΦ : Φ ≠ 0)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : ∀ α : Fin 3, α ≠ 2 →
      q₀ ≤ expectationRatioRe
        ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2)
    (hcond2 : 3 * ((1 : ℕ) : ℝ) * ((2 * m - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * m - 2 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * ((1 : ℕ) : ℝ) * ((2 * m - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * m - 3 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcondD : 3 * ((1 : ℕ) : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (htower : towerState (torusParitySublattice d L) 1 (m : ℤ) Φ ≠ 0) :
    expectationRatioRe (xyChemicalPotentialHamiltonianS d L 0)
        (towerState (torusParitySublattice d L) 1 (m : ℤ) Φ)
      ≤ E₀.re + 8 * towerEnergyCoeff d L 1 m q₀ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hVc : ((L : ℂ) ^ d) ^ m ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L)))
  have hHerm : (xyChemicalPotentialHamiltonianS d L 0).IsHermitian :=
    xyChemicalPotentialHamiltonianS_isHermitian d L 0
  have hHxy : xyChemicalPotentialHamiltonianS d L 0 = (2 : ℂ) • xyHamiltonianS d L :=
    xyChemicalPotentialHamiltonianS_zero d L
  have hAconj : Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 true ^ m)
      = staggeredOrderDensityOpS d L 1 false ^ m :=
    (orderDensityFalse_pow_eq_conjTranspose d L 1 m).symm
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L 1 Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hbase : 2 * q₀ * phatMoment d L 1 Φ 0 ≤ phatMoment d L 1 Φ 1 := by
    have h := phatMoment_one_ge_of_planar_lro d L 1 Φ q₀ (by rw [← phatMoment_zero]; exact hm0)
      hVpos hlro
    rwa [phatMoment_zero]
  have hratio : ∀ n, 2 * q₀ * phatMoment d L 1 Φ n ≤ phatMoment d L 1 Φ (n + 1) :=
    phatMoment_succ_ratio d L 1 Φ hm0 hbase
  have htwo := momentFactor_twoM_sub_two_le d L 1 m Φ hq₀ hm hratio
  have hthree := momentFactor_twoM_sub_three_le d L 1 m Φ hq₀ hm hratio
  have hnum := xy_tower_numerator_bound d L m hL Φ hsing hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  have hPM := phatMoment_nonneg d L 1 Φ m
  have hCoeff := towerEnergyCoeff_nonneg d L 1 m hq₀
  have hAne : (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ ≠ 0 := by
    intro h; apply htower; rw [towerState_pos_eq_smul, h, smul_zero]
  -- variational gap ≤ pure-XY numerator ≤ P_m · (4 · towerEnergyCoeff)
  have hgap : (star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ) ⬝ᵥ
        (xyChemicalPotentialHamiltonianS d L 0).mulVec
          ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ)).re
      - E₀.re * (star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ).re
      ≤ phatMoment d L 1 Φ m * (4 * towerEnergyCoeff d L 1 m q₀) := by
    refine (variational_gap_le_double_commutator (staggeredOrderDensityOpS d L 1 true ^ m)
      (xyChemicalPotentialHamiltonianS d L 0) hHerm Φ E₀ hev hmin hΦ).trans ?_
    rw [hAconj, hHxy]
    refine (le_abs_self _).trans (hnum.trans ?_)
    rw [show phatMoment d L 1 Φ m * (4 * towerEnergyCoeff d L 1 m q₀)
        = 4 * ((m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 4 / (L : ℝ) ^ d)
              * (phatMoment d L 1 Φ m / (2 * q₀))
            + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
                  * (phatMoment d L 1 Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))
              + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
                  * (phatMoment d L 1 Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀))))))))) from by
      unfold towerEnergyCoeff; ring]
    gcongr
  -- denominator: ½ P_m ≤ ‖(ô⁺)^m Φ‖²
  have hdeneq : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L 1 false ^ m
        * staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ
      = star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ := by
    rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
      orderDensityFalse_pow_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hden : (1 / 2) * phatMoment d L 1 Φ m
      ≤ (star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ).re := by
    rw [← hdeneq]
    exact tower_denominator_lower_bound d L 1 le_rfl Φ hsing hm0 (hratio 0) hcondD
  have hdenpos : 0 < (star ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ) ⬝ᵥ
      (staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hAne)).1
  simp only [expectationRatioRe]
  rw [towerState_pos_eq_smul,
    rayleigh_smul_invariant (xyChemicalPotentialHamiltonianS d L 0) (((L : ℂ) ^ d) ^ m) hVc
      ((staggeredOrderDensityOpS d L 1 true ^ m).mulVec Φ), div_le_iff₀ hdenpos]
  have hkey := mul_le_mul_of_nonneg_left hden
    (show (0 : ℝ) ≤ 8 * towerEnergyCoeff d L 1 m q₀ by positivity)
  nlinarith [hgap, hkey, hPM, hCoeff]

set_option maxHeartbeats 1600000 in -- large conjTranspose double-commutator identity + assembly
/-- **Half-filling lowering-tower Rayleigh bound** (Tasaki §5.3, eq. (5.3.4) at `μ = 0`, lowering
branch).  Mirror of `becTowerState_pos_rayleigh_bound_halfFilling`: the lowering tower state
`Γ_{-m} = (Ô_L^-)^m Φ` (`m ≥ 1`) obeys `⟨Γ_{-m}, Ĥ_0 Γ_{-m}⟩ / ⟨Γ_{-m}, Γ_{-m}⟩ ≤ E₀ + 8 ·
towerEnergyCoeff`.  The lowering double-commutator operator is the conjugate transpose of the
raising one (`re_dotProduct_mulVec_conjTranspose` keeps the real part), so the same numerator
bound applies; the denominator uses `tower_denominator_lower_bound_lower`. -/
theorem becTowerState_neg_rayleigh_bound_halfFilling (d L m : ℕ) [NeZero L] (hL : 2 ≤ L)
    (hm : 1 ≤ m) (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ)
    (hev : (xyChemicalPotentialHamiltonianS d L 0).mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin 2) → ℂ), Ψ ≠ 0 →
       (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    (hΦ : Φ ≠ 0)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : ∀ α : Fin 3, α ≠ 2 →
      q₀ ≤ expectationRatioRe
        ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2)
    (hcond2 : 3 * ((1 : ℕ) : ℝ) * ((2 * m - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * m - 2 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * ((1 : ℕ) : ℝ) * ((2 * m - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * m - 3 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcondD : 3 * ((1 : ℕ) : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (htower : towerState (torusParitySublattice d L) 1 (-(m : ℤ)) Φ ≠ 0) :
    expectationRatioRe (xyChemicalPotentialHamiltonianS d L 0)
        (towerState (torusParitySublattice d L) 1 (-(m : ℤ)) Φ)
      ≤ E₀.re + 8 * towerEnergyCoeff d L 1 m q₀ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hVc : ((L : ℂ) ^ d) ^ m ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L)))
  have hHerm : (xyChemicalPotentialHamiltonianS d L 0).IsHermitian :=
    xyChemicalPotentialHamiltonianS_isHermitian d L 0
  have hHconj : Matrix.conjTranspose (xyChemicalPotentialHamiltonianS d L 0)
      = xyChemicalPotentialHamiltonianS d L 0 := hHerm
  have hHxy : xyChemicalPotentialHamiltonianS d L 0 = (2 : ℂ) • xyHamiltonianS d L :=
    xyChemicalPotentialHamiltonianS_zero d L
  have hft : Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 true ^ m)
      = staggeredOrderDensityOpS d L 1 false ^ m :=
    (orderDensityFalse_pow_eq_conjTranspose d L 1 m).symm
  have hff : Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 false ^ m)
      = staggeredOrderDensityOpS d L 1 true ^ m := by
    rw [orderDensityFalse_pow_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L 1 Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hbase : 2 * q₀ * phatMoment d L 1 Φ 0 ≤ phatMoment d L 1 Φ 1 := by
    have h := phatMoment_one_ge_of_planar_lro d L 1 Φ q₀ (by rw [← phatMoment_zero]; exact hm0)
      hVpos hlro
    rwa [phatMoment_zero]
  have hratio : ∀ n, 2 * q₀ * phatMoment d L 1 Φ n ≤ phatMoment d L 1 Φ (n + 1) :=
    phatMoment_succ_ratio d L 1 Φ hm0 hbase
  have htwo := momentFactor_twoM_sub_two_le d L 1 m Φ hq₀ hm hratio
  have hthree := momentFactor_twoM_sub_three_le d L 1 m Φ hq₀ hm hratio
  have hnum := xy_tower_numerator_bound d L m hL Φ hsing hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  have hPM := phatMoment_nonneg d L 1 Φ m
  have hCoeff := towerEnergyCoeff_nonneg d L 1 m hq₀
  have hAne : (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ ≠ 0 := by
    intro h; apply htower; rw [towerState_neg_eq_smul d L 1 m hm, h, smul_zero]
  have hgap : (star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ) ⬝ᵥ
        (xyChemicalPotentialHamiltonianS d L 0).mulVec
          ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ)).re
      - E₀.re * (star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ).re
      ≤ phatMoment d L 1 Φ m * (4 * towerEnergyCoeff d L 1 m q₀) := by
    refine (variational_gap_le_double_commutator (staggeredOrderDensityOpS d L 1 false ^ m)
      (xyChemicalPotentialHamiltonianS d L 0) hHerm Φ E₀ hev hmin hΦ).trans ?_
    rw [show Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 false ^ m)
          * (xyChemicalPotentialHamiltonianS d L 0 * staggeredOrderDensityOpS d L 1 false ^ m
            - staggeredOrderDensityOpS d L 1 false ^ m * xyChemicalPotentialHamiltonianS d L 0)
          - (xyChemicalPotentialHamiltonianS d L 0 * staggeredOrderDensityOpS d L 1 false ^ m
            - staggeredOrderDensityOpS d L 1 false ^ m * xyChemicalPotentialHamiltonianS d L 0)
            * Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 false ^ m)
        = Matrix.conjTranspose (staggeredOrderDensityOpS d L 1 false ^ m
            * (xyChemicalPotentialHamiltonianS d L 0 * staggeredOrderDensityOpS d L 1 true ^ m
              - staggeredOrderDensityOpS d L 1 true ^ m * xyChemicalPotentialHamiltonianS d L 0)
          - (xyChemicalPotentialHamiltonianS d L 0 * staggeredOrderDensityOpS d L 1 true ^ m
              - staggeredOrderDensityOpS d L 1 true ^ m * xyChemicalPotentialHamiltonianS d L 0)
            * staggeredOrderDensityOpS d L 1 false ^ m) from by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hHconj, hft, hff]
      noncomm_ring, re_dotProduct_mulVec_conjTranspose, hHxy]
    refine (le_abs_self _).trans (hnum.trans ?_)
    rw [show phatMoment d L 1 Φ m * (4 * towerEnergyCoeff d L 1 m q₀)
        = 4 * ((m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 4 / (L : ℝ) ^ d)
              * (phatMoment d L 1 Φ m / (2 * q₀))
            + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
                  * (phatMoment d L 1 Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))
              + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
                  * (phatMoment d L 1 Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀))))))))) from by
      unfold towerEnergyCoeff; ring]
    gcongr
  have hdeneq : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L 1 true ^ m
        * staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ
      = star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ := by
    rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
      ← orderDensityFalse_pow_eq_conjTranspose]
  have hden : (1 / 2) * phatMoment d L 1 Φ m
      ≤ (star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ).re := by
    rw [← hdeneq]
    exact tower_denominator_lower_bound_lower d L 1 le_rfl Φ hsing hm0 (hratio 0) hcondD
  have hdenpos : 0 < (star ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ) ⬝ᵥ
      (staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hAne)).1
  simp only [expectationRatioRe]
  rw [towerState_neg_eq_smul d L 1 m hm,
    rayleigh_smul_invariant (xyChemicalPotentialHamiltonianS d L 0) (((L : ℂ) ^ d) ^ m) hVc
      ((staggeredOrderDensityOpS d L 1 false ^ m).mulVec Φ), div_le_iff₀ hdenpos]
  have hkey := mul_le_mul_of_nonneg_left hden
    (show (0 : ℝ) ≤ 8 * towerEnergyCoeff d L 1 m q₀ by positivity)
  nlinarith [hgap, hkey, hPM, hCoeff]

set_option maxHeartbeats 1600000 in -- trichotomy over M with per-branch cubic-rounding assembly
/-- **Construction of the half-filling BEC tower constants** (Tasaki §5.3, Theorem 5.2, eq. (5.3.4),
footnote 8, p. 141).  Exhibits explicit `C₁, C₂ > 0` — depending only on `d` and `q₀` — witnessing
`IsBECTowerConstantsHalfFilling d q₀ C₁ C₂` (axiom-free).  For each even `L`, half-filling ground
state `Φ` and `|M| ≤ C₁ L^{d/2}`: the tower state is nonvanishing
(`becTowerState_ne_zero_of_planar_lro`, PR-4), and (trichotomy on `M`) the Rayleigh energy obeys
the quadratic trial bound `E₀ + 8 · towerEnergyCoeff`
(`becTowerState_pos/neg_rayleigh_bound_halfFilling`), which `towerEnergyCoeff_le` sharpens to
`O(M²/L^d)` and the rounding `M² ≤ |M|³` (for `|M| ≥ 1`) casts into the faithful cubic increment
`C₂ |M|³ / L^d`.  The `M = 0` case is `Γ_0 = Φ`, Rayleigh `= E₀`.
`tower_conditions_of_le` reduces all range/budget conditions to `|M| ≤ C₁ L^{d/2}`. -/
theorem becTowerConstantsHalfFilling_of_planar_lro (d : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsBECTowerConstantsHalfFilling d q₀ C₁ C₂ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set C₁ := min (Real.sqrt (q₀ / 6))
    (Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / 16) with hC1
  have ha : 0 < Real.sqrt (q₀ / 6) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / 16 := by positivity
  have hC1pos : 0 < C₁ := lt_min ha hb
  have hsq2q : 0 < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by positivity)
  set CQ := 288 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 4 / q₀
    + 576 * C₁ ^ 2 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀ with hCQ
  have hCQpos : 0 < CQ := by
    rw [hCQ]
    have h1 : 0 < 288 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 4 / q₀ := by positivity
    have h2 : 0 ≤ 576 * C₁ ^ 2 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3
        * (1 + 1 / Real.sqrt (2 * q₀)) / q₀ := by positivity
    linarith
  have hC2pos : 0 < 4 * CQ := by linarith
  have hC1cond : 6 * ((1 : ℕ) : ℝ) * C₁ ^ 2 ≤ q₀ := by
    have h1 : C₁ ≤ Real.sqrt (q₀ / 6) := min_le_left _ _
    have h2 : C₁ ^ 2 ≤ q₀ / 6 := by
      calc C₁ ^ 2 ≤ (Real.sqrt (q₀ / 6)) ^ 2 := by nlinarith [h1, hC1pos.le]
        _ = q₀ / 6 := Real.sq_sqrt (by positivity)
    rw [Nat.cast_one]; linarith [h2]
  have hC1bud : 16 * ((1 : ℕ) : ℝ) * C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) := by
    have h1 : C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / 16 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    rw [Nat.cast_one]; linarith [h1]
  refine ⟨C₁, 4 * CQ, hC1pos, hC2pos, ?_⟩
  intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing hlro hMbound
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L 1 Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hbridge := LatticeSystem.Math.Ldhalf_bridge d L
  rw [hbridge] at hMbound
  -- the range condition `3 (M.natAbs)² ≤ 2 q₀ V` and the non-vanishing conjunct (uniform in `M`)
  obtain ⟨_, _, _, _, hcDabs⟩ :=
    tower_conditions_of_le d L 1 M.natAbs le_rfl hL hq₀ hC1cond hC1bud hMbound
  have hne := becTowerState_ne_zero_of_planar_lro d L Φ hsing hq₀ hm0 hlro M
    (by exact_mod_cast hcDabs)
  refine ⟨hne, ?_⟩
  rcases lt_trichotomy M 0 with hM | hM | hM
  · -- M < 0
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = -(m : ℤ) := ⟨M.natAbs, by omega⟩
    have hmpos : 1 ≤ m := by omega
    rw [Int.natAbs_neg, Int.natAbs_natCast] at hMbound
    have hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d := by
      nlinarith [mul_self_le_mul_self (Nat.cast_nonneg m) hMbound, Real.sq_sqrt hVpos.le,
        Real.sqrt_nonneg ((L : ℝ) ^ d), hC1pos.le]
    obtain ⟨hc2, hb2, hc3, hb3, hcD⟩ :=
      tower_conditions_of_le d L 1 m le_rfl hL hq₀ hC1cond hC1bud hMbound
    have hne' : towerState (torusParitySublattice d L) 1 (-(m : ℤ)) Φ ≠ 0 := hne
    have hmain := becTowerState_neg_rayleigh_bound_halfFilling d L m hL hmpos Φ E₀ hev hmin hΦ hsing
      hq₀ hlro hc2 hb2 hc3 hb3 hcD hne'
    have hcoeff : 2 * towerEnergyCoeff d L 1 m q₀ ≤ CQ * (m : ℝ) ^ 2 / (L : ℝ) ^ d :=
      towerEnergyCoeff_le d L 1 m hq₀ hm2
    have hnatabs : ((-(m : ℤ)).natAbs : ℝ) = (m : ℝ) := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    rw [hnatabs]
    refine le_trans hmain ?_
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hm23 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith [hm1R]
    have hc' : 2 * towerEnergyCoeff d L 1 m q₀ * (L : ℝ) ^ d ≤ CQ * (m : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hcoeff hVpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hVpos)] at h
    have hcub : 8 * towerEnergyCoeff d L 1 m q₀ ≤ 4 * CQ * (m : ℝ) ^ 3 / (L : ℝ) ^ d := by
      rw [le_div_iff₀ hVpos]
      linarith [hc', mul_le_mul_of_nonneg_left hm23 hCQpos.le]
    linarith [hcub]
  · -- M = 0: Γ_0 = Φ, Rayleigh = E₀
    subst hM
    have hHerm := xyChemicalPotentialHamiltonianS_isHermitian d L 0
    have hE0im : E₀.im = 0 := hermitian_mulVec_eigenvalue_im_zero hHerm hΦ hev
    have hΦim : (star Φ ⬝ᵥ Φ).im = 0 :=
      ((Complex.le_def.mp (dotProduct_star_self_nonneg Φ)).2).symm
    have hΓ : towerState (torusParitySublattice d L) 1 (0 : ℤ) Φ = Φ := by rw [towerState]; simp
    simp only [expectationRatioRe, Int.natAbs_zero]
    rw [hΓ, hev, dotProduct_smul, smul_eq_mul, Complex.mul_re, hE0im, hΦim]
    rw [show E₀.re * (star Φ ⬝ᵥ Φ).re - 0 * 0 = E₀.re * (star Φ ⬝ᵥ Φ).re by ring,
      mul_div_assoc, div_self (ne_of_gt hm0c), mul_one]
    simp
  · -- M > 0
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = (m : ℤ) := ⟨M.natAbs, by omega⟩
    have hmpos : 1 ≤ m := by omega
    rw [Int.natAbs_natCast] at hMbound
    have hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d := by
      nlinarith [mul_self_le_mul_self (Nat.cast_nonneg m) hMbound, Real.sq_sqrt hVpos.le,
        Real.sqrt_nonneg ((L : ℝ) ^ d), hC1pos.le]
    obtain ⟨hc2, hb2, hc3, hb3, hcD⟩ :=
      tower_conditions_of_le d L 1 m le_rfl hL hq₀ hC1cond hC1bud hMbound
    have hne' : towerState (torusParitySublattice d L) 1 (m : ℤ) Φ ≠ 0 := hne
    have hmain := becTowerState_pos_rayleigh_bound_halfFilling d L m hL hmpos Φ E₀ hev hmin hΦ hsing
      hq₀ hlro hc2 hb2 hc3 hb3 hcD hne'
    have hcoeff : 2 * towerEnergyCoeff d L 1 m q₀ ≤ CQ * (m : ℝ) ^ 2 / (L : ℝ) ^ d :=
      towerEnergyCoeff_le d L 1 m hq₀ hm2
    rw [Int.natAbs_natCast]
    refine le_trans hmain ?_
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hm23 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith [hm1R]
    have hc' : 2 * towerEnergyCoeff d L 1 m q₀ * (L : ℝ) ^ d ≤ CQ * (m : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hcoeff hVpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hVpos)] at h
    have hcub : 8 * towerEnergyCoeff d L 1 m q₀ ≤ 4 * CQ * (m : ℝ) ^ 3 / (L : ℝ) ^ d := by
      rw [le_div_iff₀ hVpos]
      linarith [hc', mul_le_mul_of_nonneg_left hm23 hCQpos.le]
    linarith [hcub]

/-- **Tasaki Theorem 5.2 at half filling (`μ = 0`), PROVED axiom-free** (eq. (5.3.4), footnote 8,
p. 141).  For the spin-`1/2` XY model (the `u ↑ ∞` hard-core boson model) on the `d`-dimensional
hypercubic torus with `d ≥ 2`, at half filling `ρ = 1/2` (the `μ = 0`, `Ŝ_tot^{(3)} = 0` sector),
there exist constants `C₁, C₂ > 0` such that `IsBECTowerConstantsHalfFilling d q₀ C₁ C₂` holds: for
every even `L ≥ 2` and every ground state `Φ_GS` of the half-filling Hamiltonian `Ĥ_0 = 2 Ĥ_XY` in
the `Ŝ_tot^{(3)} = 0` sector exhibiting the two XY-plane ODLRO bounds (`α = 1, 2`) with parameter
`q₀`, the bosonic tower states `Γ_M = (Ô_L^{sgn M})^{|M|} Φ_GS` (for `|M| ≤ C₁ L^{d/2}`) are
**nonvanishing and** low-lying with the **cubic** energy increment
`⟨Γ_M, Ĥ_0 Γ_M⟩ / ⟨Γ_M, Γ_M⟩ ≤ E₀ + C₂ |M|³ / L^d`.

This is the axiom-free half-filling kernel of Theorem 5.2: it closes the existential of
`becTowerConstantsHalfFilling_of_planar_lro`, whose `#print axioms` is `[propext, Classical.choice,
Quot.sound]` only.  The general-`μ` statement is kept as the faithful documented axiom
`tasaki_5_2_bec_tower`: at `μ ≠ 0` a ground state carries `Ŝ_tot^{(3)} Φ = s₀ ≠ 0`, so the reused
variational bricks (denominator, numerator, non-vanishing) — all requiring the half-filling sector —
no longer close, and the general-`μ` bound rests on the Koma–Tasaki [21] `d`-dimensional
reflection-positivity/infrared machinery, the same RP-intractability exception as Theorem 5.1,
intractable at project scale.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eq. (5.3.4), footnote 8, p. 141 (Koma–Tasaki [21]). -/
theorem tasaki_5_2_bec_tower_half_filling (d : ℕ) (hd : 2 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsBECTowerConstantsHalfFilling d q₀ C₁ C₂ :=
  becTowerConstantsHalfFilling_of_planar_lro d (by omega) q₀ hq₀

end LatticeSystem.Quantum
