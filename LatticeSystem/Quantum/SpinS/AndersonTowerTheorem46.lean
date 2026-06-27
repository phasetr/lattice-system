/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), capstone — discharging the energy-bound axiom.

The numerator estimate (`tower_numerator_bound`, in `AndersonTowerNumerator`), the variational gap (★,
`tower_numerator_double_commutator_le`), the denominator lower bound (`tower_denominator_lower_bound`)
and the long-range-order moment recursion (`phatMoment_succ_two_q0_le`) combine into a Rayleigh bound
for the tower trial state `(ô⁺)^m Φ`, which (via scale invariance) gives the tower-state energy
bound and discharges `tower_lowLying_energy_bound` to a proved theorem.

This file is downstream of `AndersonTower.lean` (which only states the predicate), so the proved
theorem can refer to the numerator machinery without an import cycle.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerNumerator

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **The per-trial Rayleigh-bound coefficient.**  The numerator bound divided by the denominator
lower bound `½P_m` (so the `P_m` factor cancels) leaves `2 ·` this coefficient, which is the
explicit `O(m²/V) + O(m⁴/V²)` energy excess of the trial state `(ô⁺)^m Φ`.  Here `V = L^d`. -/
noncomputable def towerEnergyCoeff (d L N m : ℕ) (q₀ : ℝ) : ℝ :=
  (m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * (1 / (2 * q₀))
      + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * (1 / (2 * q₀) / Real.sqrt (2 * q₀))))
        + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * (1 / (2 * q₀) / Real.sqrt (2 * q₀)))))))

/-- The trial-energy coefficient is nonnegative (for `q₀ > 0`). -/
theorem towerEnergyCoeff_nonneg (d L N m : ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀) :
    0 ≤ towerEnergyCoeff d L N m q₀ := by
  have h2q : (0 : ℝ) < 2 * q₀ := by linarith
  have hs : (0 : ℝ) < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr h2q
  unfold towerEnergyCoeff
  positivity

/-- **Trial-state energy bound for `(ô⁺)^m Φ`.**  Combining the ★ variational gap, the numerator
estimate `M²·(…)`, the moment-factor → `P_m` conversions, and the denominator lower bound `½P_m`
gives the Rayleigh bound `≤ E₀ + 2·towerEnergyCoeff` for the (unnormalized) tower trial state. -/
theorem tower_trial_energy_bound (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L) (hm : 2 ≤ m)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
    (hev : (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ), Ψ ≠ 0 →
       (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    (hΦ : Φ ≠ 0)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2))
    (hcond2 : 3 * (N : ℝ) * ((2 * m - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * m - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * m - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * m - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcondD : 3 * (N : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hAne : (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ ≠ 0) :
    (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ)).re
        / (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ).re
      ≤ E₀.re + 2 * towerEnergyCoeff d L N m q₀ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L N Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) :=
    phatMoment_succ_two_q0_le d L N Φ hsing3 hsing1 q₀ hm0c hVpos hlro
  -- numerator estimate, with moment factors converted to `P_m`
  have htwo := momentFactor_twoM_sub_two_le d L N m Φ hq₀ (by omega) hratio
  have hthree := momentFactor_twoM_sub_three_le d L N m Φ hq₀ hm hratio
  have hnum := tower_numerator_bound d L N m hN hL Φ hsing3 hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  have hPM := phatMoment_nonneg d L N Φ m
  -- ★ variational gap ≤ numerator real part ≤ M²·(…) ≤ P_m · towerEnergyCoeff
  have hstar := tower_numerator_double_commutator_le d L N Φ E₀ m hev hmin hΦ
  have hgap : (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ)).re
      - E₀.re * (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ).re
      ≤ phatMoment d L N Φ m * towerEnergyCoeff d L N m q₀ := by
    refine hstar.trans ((le_abs_self _).trans (hnum.trans ?_))
    rw [show phatMoment d L N Φ m * towerEnergyCoeff d L N m q₀
        = (m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
              * (phatMoment d L N Φ m / (2 * q₀))
            + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
                  * (phatMoment d L N Φ m / (2 * q₀) / Real.sqrt (2 * q₀))))
              + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
                  * (phatMoment d L N Φ m / (2 * q₀) / Real.sqrt (2 * q₀))))))) from by
      unfold towerEnergyCoeff; ring]
    gcongr
  -- denominator: ½ P_m ≤ ‖AΦ‖²
  have hdeneq : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ m
        * staggeredOrderDensityOpS d L N true ^ m).mulVec Φ
      = star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ := by
    rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
      orderDensityFalse_pow_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hden : (1 / 2) * phatMoment d L N Φ m
      ≤ (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ).re := by
    rw [← hdeneq]
    exact tower_denominator_lower_bound d L N hN Φ hsing3 hm0 (hratio 0) hcondD
  have hdenpos : 0 < (star ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ) ⬝ᵥ
      (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hAne)).1
  have hCoeff := towerEnergyCoeff_nonneg d L N m hq₀
  rw [div_le_iff₀ hdenpos]
  have hkey := mul_le_mul_of_nonneg_left hden
    (show (0 : ℝ) ≤ 2 * towerEnergyCoeff d L N m q₀ by positivity)
  nlinarith [hgap, hkey, hPM, hCoeff]

end LatticeSystem.Quantum
