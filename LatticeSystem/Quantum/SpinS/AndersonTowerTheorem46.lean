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

/-- **General variational gap ≤ double commutator.**  For a Hermitian `H` with ground state
`H Φ = E₀ Φ` (`E₀` minimal) and any operator `A`, the trial-state energy gap is bounded by the
symmetric double commutator with `Aᴴ`: `⟨AΦ,H AΦ⟩ − E₀⟨AΦ,AΦ⟩ ≤ ⟨Φ, [Aᴴ,[H,A]] Φ⟩`.  This is the
operator-agnostic form of `tower_numerator_double_commutator_le` (which it generalizes from
`A = (ô⁺)^M` to arbitrary `A`), used for both the raising (`A = (ô⁺)^m`) and lowering
(`A = (ô⁻)^m`) towers. -/
theorem variational_gap_le_double_commutator {n : Type*} [Fintype n] [Nonempty n]
    (A H : Matrix n n ℂ) (hHerm : H.IsHermitian) (Φ : n → ℂ) (E₀ : ℂ)
    (hev : H.mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : n → ℂ), Ψ ≠ 0 → H.mulVec Ψ = E • Ψ → E₀.re ≤ E.re) (hΦ : Φ ≠ 0) :
    (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ)).re
        - E₀.re * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ).re
      ≤ (star Φ ⬝ᵥ (Matrix.conjTranspose A * (H * A - A * H)
          - (H * A - A * H) * Matrix.conjTranspose A).mulVec Φ).re := by
  classical
  set Adag := Matrix.conjTranspose A with hAd
  have hE₀im : E₀.im = 0 := hermitian_mulVec_eigenvalue_im_zero hHerm hΦ hev
  have hT1 : star Φ ⬝ᵥ (Adag * (H * A)).mulVec Φ
      = star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ) := by
    rw [← Matrix.mulVec_mulVec, hAd, star_dotProduct_mulVec_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec]
  have hT2 : star Φ ⬝ᵥ (Adag * A * H).mulVec Φ
      = E₀ * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hAd,
      star_dotProduct_mulVec_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hconjE : (star E₀ : ℂ) = E₀ := by
    rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hE₀im
  have hT3 : star Φ ⬝ᵥ (H * A * Adag).mulVec Φ
      = E₀ * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ) := by
    rw [mul_assoc, hermitian_dotProduct_shift hHerm, hev, star_smul, smul_dotProduct, hconjE,
      smul_eq_mul, ← Matrix.mulVec_mulVec, hAd, star_dotProduct_mulVec_conjTranspose]
  have hT4 : star Φ ⬝ᵥ (A * H * Adag).mulVec Φ
      = star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ) := by
    rw [mul_assoc, ← Matrix.mulVec_mulVec, hAd, star_dotProduct_mulVec_conjTranspose,
      Matrix.mulVec_mulVec]
  have hP : Adag * (H * A - A * H) - (H * A - A * H) * Adag
      = Adag * (H * A) - Adag * A * H - H * A * Adag + A * H * Adag := by noncomm_ring
  have heq : star Φ ⬝ᵥ (Adag * (H * A - A * H) - (H * A - A * H) * Adag).mulVec Φ
      = (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ) - E₀ * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ))
        + (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)
            - E₀ * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ)) := by
    rw [hP]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
      hT1, hT2, hT3, hT4]
    ring
  have hself1 : (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ).im = 0 :=
    ((Complex.le_def.mp (dotProduct_star_self_nonneg (A.mulVec Φ))).2).symm
  have hself2 : (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).im = 0 :=
    ((Complex.le_def.mp (dotProduct_star_self_nonneg (Adag.mulVec Φ))).2).symm
  have hre : (star Φ ⬝ᵥ (Adag * (H * A - A * H) - (H * A - A * H) * Adag).mulVec Φ).re
      = (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ)).re
          - E₀.re * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ).re
        + ((star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re
          - E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re) := by
    rw [heq]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, hE₀im, hself1, hself2]
    ring
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHerm (Adag.mulVec Φ)
  obtain ⟨v, hv_ne, hv_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHerm
  have hE₀le : E₀.re ≤ hermitianMinEigenvalue hHerm := by
    have := hmin ((hermitianMinEigenvalue hHerm : ℝ) : ℂ) v hv_ne hv_eig
    simpa using this
  have hdenom : 0 ≤ (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re :=
    (Complex.le_def.mp (dotProduct_star_self_nonneg (Adag.mulVec Φ))).1
  have hnumgap_dag : 0 ≤ (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re
      - E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re := by
    have h1 : E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re
        ≤ hermitianMinEigenvalue hHerm * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re :=
      mul_le_mul_of_nonneg_right hE₀le hdenom
    have h2 : hermitianMinEigenvalue hHerm * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re
        ≤ rayleighOnVec H (Adag.mulVec Φ) := hvar
    have h3 : rayleighOnVec H (Adag.mulVec Φ)
        = (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re := rfl
    linarith
  rw [hre]
  linarith

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

/-- **Tower-state energy bound for `M = m ≥ 0`.**  The raising tower state
`towerState m Φ = V^m·(ô⁺)^m Φ` has the same Rayleigh quotient as `(ô⁺)^m Φ` (scale invariance), so
`tower_trial_energy_bound` transfers verbatim. -/
theorem towerState_pos_rayleigh_bound (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (hm : 2 ≤ m)
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
    (htower : towerState (torusParitySublattice d L) N (m : ℤ) Φ ≠ 0) :
    (star (towerState (torusParitySublattice d L) N (m : ℤ) Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          (towerState (torusParitySublattice d L) N (m : ℤ) Φ)).re
        / (star (towerState (torusParitySublattice d L) N (m : ℤ) Φ) ⬝ᵥ
          towerState (torusParitySublattice d L) N (m : ℤ) Φ).re
      ≤ E₀.re + 2 * towerEnergyCoeff d L N m q₀ := by
  have hVc : ((L : ℂ) ^ d) ^ m ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L)))
  have hAne : (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ ≠ 0 := by
    intro h
    apply htower
    rw [towerState_pos_eq_smul, h, smul_zero]
  rw [towerState_pos_eq_smul,
    rayleigh_smul_invariant (heisenbergHamiltonianS (torusNNCoupling d L) N)
      (((L : ℂ) ^ d) ^ m) hVc ((staggeredOrderDensityOpS d L N true ^ m).mulVec Φ)]
  exact tower_trial_energy_bound d L N m hN hL hm Φ E₀ hev hmin hΦ hsing3 hsing1 hq₀ hlro
    hcond2 hbudget2 hcond3 hbudget3 hcondD hAne

/-- **The trial bounds `hcond2/3`, `hbudget2/3`, `hcondD` from a single size constraint.**  If
`m ≤ C₁·√V` with `6N C₁² ≤ q₀` (handles all `3N(2m)² ≤ 2q₀V` conditions) and
`16N C₁ ≤ √(2^d)·√(2q₀)` (handles all budget conditions, using `√V ≥ √(2^d)`), then every condition
the numerator/denominator bounds need holds. -/
theorem tower_conditions_of_le (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L) {q₀ C₁ : ℝ}
    (hq₀ : 0 < q₀) (hC1cond : 6 * (N : ℝ) * C₁ ^ 2 ≤ q₀)
    (hC1bud : 16 * (N : ℝ) * C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀))
    (hm : (m : ℝ) ≤ C₁ * Real.sqrt ((L : ℝ) ^ d)) :
    (3 * (N : ℝ) * ((2 * m - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
      ∧ (((2 * m - 2 : ℕ) : ℝ) * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
      ∧ (3 * (N : ℝ) * ((2 * m - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
      ∧ (((2 * m - 3 : ℕ) : ℝ) * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
      ∧ (3 * (N : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) := by
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hsqVsq : Real.sqrt ((L : ℝ) ^ d) ^ 2 = (L : ℝ) ^ d := Real.sq_sqrt hVpos.le
  have hsqVnn : (0 : ℝ) ≤ Real.sqrt ((L : ℝ) ^ d) := Real.sqrt_nonneg _
  have hsq2q : (0 : ℝ) < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by linarith)
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- m² ≤ C₁²·V
  have hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d := by
    have := mul_self_le_mul_self hmnn hm
    nlinarith [this, hsqVsq]
  -- common condition `3N(2m)² ≤ 2q₀V`, hence the `2m-2`, `2m-3`, `m` cases
  have hcond2m : 3 * (N : ℝ) * (2 * (m : ℝ)) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    have h1 : 12 * (N : ℝ) * (m : ℝ) ^ 2 ≤ 12 * (N : ℝ) * (C₁ ^ 2 * (L : ℝ) ^ d) := by
      nlinarith [hm2, hNnn]
    nlinarith [h1, hC1cond, hVpos.le]
  have hsub2 : ((2 * m - 2 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast Nat.sub_le (2 * m) 2
  have hsub3 : ((2 * m - 3 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast Nat.sub_le (2 * m) 3
  have hsub2nn : (0 : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub3nn : (0 : ℝ) ≤ ((2 * m - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- √V ≥ √(2^d)
  have hVge : Real.sqrt ((2 : ℝ) ^ d) ≤ Real.sqrt ((L : ℝ) ^ d) :=
    Real.sqrt_le_sqrt (by gcongr)
  have h16 : 16 * (N : ℝ) * C₁ ≤ Real.sqrt ((L : ℝ) ^ d) * Real.sqrt (2 * q₀) :=
    hC1bud.trans (mul_le_mul_of_nonneg_right hVge hsq2q.le)
  -- budget chain helper: `(2m-k)·(4N/(V√(2q₀))) ≤ 1/2`
  have hbud : ∀ a : ℝ, 0 ≤ a → a ≤ 2 * (m : ℝ) →
      a * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 := by
    intro a hann haub
    rw [div_div, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    -- goal: a * (2*2*N) ≤ 1/2 * (V * √(2q₀))
    have ha2C : a ≤ 2 * (C₁ * Real.sqrt ((L : ℝ) ^ d)) := by nlinarith [haub, hm]
    have hp1 : a * (2 * 2 * (N : ℝ))
        ≤ 2 * (C₁ * Real.sqrt ((L : ℝ) ^ d)) * (2 * 2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right ha2C (by positivity)
    have hp2 : Real.sqrt ((L : ℝ) ^ d) * (16 * (N : ℝ) * C₁)
        ≤ Real.sqrt ((L : ℝ) ^ d) * (Real.sqrt ((L : ℝ) ^ d) * Real.sqrt (2 * q₀)) :=
      mul_le_mul_of_nonneg_left h16 hsqVnn
    nlinarith [hp1, hp2, hsqVsq]
  refine ⟨?_, hbud _ hsub2nn hsub2, ?_, hbud _ hsub3nn hsub3, ?_⟩
  · nlinarith [hcond2m, mul_self_le_mul_self hsub2nn hsub2, hNnn]
  · nlinarith [hcond2m, mul_self_le_mul_self hsub3nn hsub3, hNnn]
  · nlinarith [hcond2m, sq_nonneg (m : ℝ), hNnn]

/-- **The trial-energy coefficient is `O(m²/V)`.**  Under the size constraint `m² ≤ C₁²V`, the
`O(m⁴/V²)` part is absorbed into the `O(m²/V)` part, giving
`2·towerEnergyCoeff ≤ C₂·m²/V` with the explicit constant
`C₂ = 288 d N⁴/q₀ + 576 C₁² d N³/(q₀√(2q₀))`. -/
theorem towerEnergyCoeff_le (d L N m : ℕ) [NeZero L] {q₀ C₁ : ℝ} (hq₀ : 0 < q₀)
    (hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d) :
    2 * towerEnergyCoeff d L N m q₀
      ≤ (288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀
          + 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 / (q₀ * Real.sqrt (2 * q₀)))
        * (m : ℝ) ^ 2 / (L : ℝ) ^ d := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by linarith)
  have hm4 : (m : ℝ) ^ 4 ≤ C₁ ^ 2 * (m : ℝ) ^ 2 * (L : ℝ) ^ d := by
    nlinarith [hm2, sq_nonneg ((m : ℝ) ^ 2)]
  have hsplit : 2 * towerEnergyCoeff d L N m q₀
      = 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 / (q₀ * Real.sqrt (2 * q₀))
          * ((m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2) := by
    rw [towerEnergyCoeff]
    field_simp
    ring
  have hmd : (m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2 ≤ C₁ ^ 2 * ((m : ℝ) ^ 2 / (L : ℝ) ^ d) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hVpos 2) hVpos]
    nlinarith [hm4, hVpos]
  calc 2 * towerEnergyCoeff d L N m q₀
      = 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 / (q₀ * Real.sqrt (2 * q₀))
          * ((m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2) := hsplit
    _ ≤ 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 / (q₀ * Real.sqrt (2 * q₀))
          * (C₁ ^ 2 * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)) := by gcongr
    _ = (288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀
          + 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 / (q₀ * Real.sqrt (2 * q₀)))
        * (m : ℝ) ^ 2 / (L : ℝ) ^ d := by ring

end LatticeSystem.Quantum
