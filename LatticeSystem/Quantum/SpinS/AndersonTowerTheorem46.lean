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

/-- **Real part is conjugation-symmetric.**  `Re⟨Φ, Bᴴ Φ⟩ = Re⟨Φ, B Φ⟩` (the sesquilinear form of
`Bᴴ` is the conjugate of that of `B`).  Used to transfer the raising numerator bound to the lowering
tower, whose numerator operator is the conjugate transpose of the raising one. -/
theorem re_dotProduct_mulVec_conjTranspose {n : Type*} [Fintype n] (B : Matrix n n ℂ) (Φ : n → ℂ) :
    (star Φ ⬝ᵥ (Matrix.conjTranspose B).mulVec Φ).re = (star Φ ⬝ᵥ B.mulVec Φ).re := by
  rw [star_dotProduct_mulVec_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.star_dotProduct, Complex.star_def, Complex.conj_re]

/-- **Lowering-tower denominator lower bound.**  Mirror of `tower_denominator_lower_bound` for the
lowering balanced word `(ô⁺)^M (ô⁻)^M`: `½P_M ≤ ‖(ô⁻)^M Φ‖²` via `orderWord_balanced_re_close`. -/
theorem tower_denominator_lower_bound_lower (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    {M : ℕ} (hcond : 3 * (N : ℝ) * (M : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    (1 / 2) * phatMoment d L N Φ M
      ≤ (star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N true ^ M
          * staggeredOrderDensityOpS d L N false ^ M).mulVec Φ).re := by
  have hwt : (List.replicate M true ++ List.replicate M false).count true = M := by
    simp [List.count_append, List.count_replicate]
  have hwf : (List.replicate M true ++ List.replicate M false).count false = M := by
    simp [List.count_append, List.count_replicate]
  have heq : orderWordProd d L N (List.replicate M true ++ List.replicate M false)
      = staggeredOrderDensityOpS d L N true ^ M * staggeredOrderDensityOpS d L N false ^ M := by
    rw [orderWordProd, List.map_append, List.map_replicate, List.map_replicate, List.prod_append,
      List.prod_replicate, List.prod_replicate]
  have hclose := orderWord_balanced_re_close d L N hN Φ hsing hm0 hlro M hcond
    (List.replicate M true ++ List.replicate M false) hwt hwf
  rw [abs_le] at hclose
  rw [← heq]
  linarith [hclose.1]

/-- **The per-trial Rayleigh-bound coefficient.**  The numerator bound divided by the denominator
lower bound `½P_m` (so the `P_m` factor cancels) leaves `2 ·` this coefficient, which is the
explicit `O(m²/V) + O(m⁴/V²)` energy excess of the trial state `(ô⁺)^m Φ`.  Here `V = L^d`. -/
noncomputable def towerEnergyCoeff (d L N m : ℕ) (q₀ : ℝ) : ℝ :=
  (m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * (1 / (2 * q₀))
      + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * (1 / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))
        + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * (1 / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀))))))))

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
theorem tower_trial_energy_bound (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L) (hm : 1 ≤ m)
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
                  * (phatMoment d L N Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))
              + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
                  * (phatMoment d L N Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))))) from by
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

set_option maxHeartbeats 1600000 in -- large noncomm_ring conjTranspose identity on a 4-term operator
/-- **Trial-state energy bound for the lowering tower `(ô⁻)^m Φ`.**  Mirror of
`tower_trial_energy_bound`: the lowering numerator operator is the conjugate transpose of the
raising one (`re_dotProduct_mulVec_conjTranspose` keeps the real part), so the same numerator bound
applies; the denominator uses `tower_denominator_lower_bound_lower`. -/
theorem tower_trial_energy_bound_lower (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (hm : 1 ≤ m) (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
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
    (hAne : (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ ≠ 0) :
    (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ)).re
        / (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ).re
      ≤ E₀.re + 2 * towerEnergyCoeff d L N m q₀ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L N Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) :=
    phatMoment_succ_two_q0_le d L N Φ hsing3 hsing1 q₀ hm0c hVpos hlro
  have htwo := momentFactor_twoM_sub_two_le d L N m Φ hq₀ (by omega) hratio
  have hthree := momentFactor_twoM_sub_three_le d L N m Φ hq₀ hm hratio
  have hnum := tower_numerator_bound d L N m hN hL Φ hsing3 hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  have hPM := phatMoment_nonneg d L N Φ m
  have hHh : Matrix.conjTranspose (heisenbergHamiltonianS (torusNNCoupling d L) N)
      = heisenbergHamiltonianS (torusNNCoupling d L) N :=
    heisenbergHamiltonianS_torus_isHermitian d L N
  have hft : Matrix.conjTranspose (staggeredOrderDensityOpS d L N true ^ m)
      = staggeredOrderDensityOpS d L N false ^ m :=
    (orderDensityFalse_pow_eq_conjTranspose d L N m).symm
  have hff : Matrix.conjTranspose (staggeredOrderDensityOpS d L N false ^ m)
      = staggeredOrderDensityOpS d L N true ^ m := by
    rw [orderDensityFalse_pow_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hgap : (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ)).re
      - E₀.re * (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ).re
      ≤ phatMoment d L N Φ m * towerEnergyCoeff d L N m q₀ := by
    refine (variational_gap_le_double_commutator (staggeredOrderDensityOpS d L N false ^ m)
      (heisenbergHamiltonianS (torusNNCoupling d L) N) hHh Φ E₀ hev hmin hΦ).trans ?_
    rw [show Matrix.conjTranspose (staggeredOrderDensityOpS d L N false ^ m)
          * (heisenbergHamiltonianS (torusNNCoupling d L) N
              * staggeredOrderDensityOpS d L N false ^ m
            - staggeredOrderDensityOpS d L N false ^ m
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          - (heisenbergHamiltonianS (torusNNCoupling d L) N
              * staggeredOrderDensityOpS d L N false ^ m
            - staggeredOrderDensityOpS d L N false ^ m
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
            * Matrix.conjTranspose (staggeredOrderDensityOpS d L N false ^ m)
        = Matrix.conjTranspose (staggeredOrderDensityOpS d L N false ^ m
            * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true ^ m
              - staggeredOrderDensityOpS d L N true ^ m
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
          - (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true ^ m
              - staggeredOrderDensityOpS d L N true ^ m
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
            * staggeredOrderDensityOpS d L N false ^ m) from by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hHh, hft, hff]
      noncomm_ring, re_dotProduct_mulVec_conjTranspose]
    refine (le_abs_self _).trans (hnum.trans ?_)
    rw [show phatMoment d L N Φ m * towerEnergyCoeff d L N m q₀
        = (m : ℝ) * ((m : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
              * (phatMoment d L N Φ m / (2 * q₀))
            + ((m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
                  * (phatMoment d L N Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))
              + (m : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (m : ℝ)))
                * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
                  * (phatMoment d L N Φ m / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)))))))) from by
      unfold towerEnergyCoeff; ring]
    gcongr
  have hdeneq : star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N true ^ m
        * staggeredOrderDensityOpS d L N false ^ m).mulVec Φ
      = star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ := by
    rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
      ← orderDensityFalse_pow_eq_conjTranspose]
  have hden : (1 / 2) * phatMoment d L N Φ m
      ≤ (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ).re := by
    rw [← hdeneq]
    exact tower_denominator_lower_bound_lower d L N hN Φ hsing3 hm0 (hratio 0) hcondD
  have hdenpos : 0 < (star ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ) ⬝ᵥ
      (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ).re :=
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
    (hm : 1 ≤ m)
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

/-- The staggered lowering operator is `V` times the per-volume lowering density: `Ô⁻ = V ô⁻`. -/
theorem staggeredLoweringOpS_eq_smul (d L N : ℕ) [NeZero L] :
    staggeredLoweringOpS (torusParitySublattice d L) N
      = ((L : ℂ) ^ d) • staggeredOrderDensityOpS d L N false := by
  rw [show staggeredOrderDensityOpS d L N false
      = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))), one_smul]

/-- The lowering tower state factors as a scalar multiple of the lowering density power:
`towerState (-(m:ℤ)) Φ = V^m · (ô⁻)^m Φ`. -/
theorem towerState_neg_eq_smul (d L N m : ℕ) [NeZero L] (hm : 1 ≤ m)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ
      = ((L : ℂ) ^ d) ^ m • (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ := by
  rw [towerState, if_neg (by omega : ¬ (0 : ℤ) ≤ -(m : ℤ)), Int.natAbs_neg, Int.natAbs_natCast,
    staggeredLoweringOpS_eq_smul, smul_pow, Matrix.smul_mulVec]

/-- **Tower-state energy bound for `M = -(m) < 0`.**  The lowering tower state
`towerState (-(m:ℤ)) Φ = V^m·(ô⁻)^m Φ` has the same Rayleigh quotient as `(ô⁻)^m Φ` (scale
invariance), so `tower_trial_energy_bound_lower` transfers verbatim. -/
theorem towerState_neg_rayleigh_bound (d L N m : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (hm : 1 ≤ m) (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
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
    (htower : towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ ≠ 0) :
    (star (towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          (towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ)).re
        / (star (towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ) ⬝ᵥ
          towerState (torusParitySublattice d L) N (-(m : ℤ)) Φ).re
      ≤ E₀.re + 2 * towerEnergyCoeff d L N m q₀ := by
  have hVc : ((L : ℂ) ^ d) ^ m ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L)))
  have hAne : (staggeredOrderDensityOpS d L N false ^ m).mulVec Φ ≠ 0 := by
    intro h
    apply htower
    rw [towerState_neg_eq_smul d L N m (by omega), h, smul_zero]
  rw [towerState_neg_eq_smul d L N m (by omega),
    rayleigh_smul_invariant (heisenbergHamiltonianS (torusNNCoupling d L) N)
      (((L : ℂ) ^ d) ^ m) hVc ((staggeredOrderDensityOpS d L N false ^ m).mulVec Φ)]
  exact tower_trial_energy_bound_lower d L N m hN hL hm Φ E₀ hev hmin hΦ hsing3 hsing1 hq₀ hlro
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
`C₂ = 288 d N⁴/q₀ + 576 C₁² d N³ (1 + 1/√(2q₀))/q₀`. -/
theorem towerEnergyCoeff_le (d L N m : ℕ) [NeZero L] {q₀ C₁ : ℝ} (hq₀ : 0 < q₀)
    (hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d) :
    2 * towerEnergyCoeff d L N m q₀
      ≤ (288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀
          + 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀)
        * (m : ℝ) ^ 2 / (L : ℝ) ^ d := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by linarith)
  have hm4 : (m : ℝ) ^ 4 ≤ C₁ ^ 2 * (m : ℝ) ^ 2 * (L : ℝ) ^ d := by
    nlinarith [hm2, sq_nonneg ((m : ℝ) ^ 2)]
  have hsplit : 2 * towerEnergyCoeff d L N m q₀
      = 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀
          * ((m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2) := by
    rw [towerEnergyCoeff]
    field_simp
    ring
  have hmd : (m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2 ≤ C₁ ^ 2 * ((m : ℝ) ^ 2 / (L : ℝ) ^ d) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hVpos 2) hVpos]
    nlinarith [hm4, hVpos]
  have hc2nn : (0 : ℝ) ≤ 576 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀ := by
    positivity
  calc 2 * towerEnergyCoeff d L N m q₀
      = 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀
          * ((m : ℝ) ^ 4 / ((L : ℝ) ^ d) ^ 2) := hsplit
    _ ≤ 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)
        + 576 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀
          * (C₁ ^ 2 * ((m : ℝ) ^ 2 / (L : ℝ) ^ d)) := by gcongr
    _ = (288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀
          + 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀)
        * (m : ℝ) ^ 2 / (L : ℝ) ^ d := by ring

/-- **Tasaki Theorem 4.6 (Anderson's tower of low-lying states), PROVED.**  Discharges the former
`tower_lowLying_energy_bound` axiom: there exist positive constants `C₁`, `C₂` (depending only on
`d`, `S = N/2`, `q₀`) such that, for every even torus side `L ≥ 2`, every total-spin-singlet ground
state `Φ` with long-range order `≥ q₀`, and every `M` with `|M| ≤ C₁ L^{d/2}` and nonzero tower
state, the tower-state Rayleigh energy obeys `≤ E₀ + C₂ M²/L^d`.  For `N = 0` the order op vanishes,
so the LRO premise is unsatisfiable and the statement is vacuous. -/
theorem tower_lowLying_energy_bound (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- N = 0: spin-0, order operator vanishes, LRO premise unsatisfiable → vacuous
    subst hN0
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hlro hMbound htower
    exfalso
    have hO0 : staggeredOrderOpS (torusParitySublattice d L) 0 = 0 := by
      rw [staggeredOrderOpS]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [spinSSiteOp3, show spinSOp3 0 = 0 from by
        ext i j; rw [spinSOp3, Matrix.diagonal_apply]
        rcases eq_or_ne i j with h | h
        · subst h; simp
        · simp [h], onSiteS_zero, smul_zero]
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
      (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
    rw [hO0] at hlro
    simp only [zero_mul, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re, zero_div] at hlro
    linarith [hlro]
  · -- N ≥ 1
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    set C₁ := min (Real.sqrt (q₀ / (6 * N)))
      (Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N)) with hC1
    set C₂ := 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀
      + 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀ with hC2
    have ha : 0 < Real.sqrt (q₀ / (6 * N)) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 < Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N) := by positivity
    have hC1pos : 0 < C₁ := lt_min ha hb
    have hsq2q : 0 < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by positivity)
    have hC2pos : 0 < C₂ := by
      rw [hC2]
      have h1 : 0 < 288 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ := by positivity
      have h2 : 0 ≤ 576 * C₁ ^ 2 * (d : ℝ) * (N : ℝ) ^ 3 * (1 + 1 / Real.sqrt (2 * q₀)) / q₀ := by
        positivity
      linarith
    have hC1cond : 6 * (N : ℝ) * C₁ ^ 2 ≤ q₀ := by
      have h1 : C₁ ≤ Real.sqrt (q₀ / (6 * N)) := min_le_left _ _
      have h2 : C₁ ^ 2 ≤ q₀ / (6 * N) := by
        calc C₁ ^ 2 ≤ (Real.sqrt (q₀ / (6 * N))) ^ 2 := by nlinarith [h1, hC1pos.le]
          _ = q₀ / (6 * N) := Real.sq_sqrt (by positivity)
      have h3 : 6 * (N : ℝ) * (q₀ / (6 * N)) = q₀ := by field_simp
      nlinarith [h2, hNR]
    have hC1bud : 16 * (N : ℝ) * C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) := by
      have h1 : C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      linarith [h1]
    refine ⟨C₁, C₂, hC1pos, hC2pos, ?_⟩
    intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hlro hMbound htower
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    have hbridge : (L : ℝ) ^ ((d : ℝ) / 2) = Real.sqrt ((L : ℝ) ^ d) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (L : ℝ) d, ← Real.rpow_mul hLpos.le]
      congr 1
      ring
    rw [hbridge] at hMbound
    rcases lt_trichotomy M 0 with hM | hM | hM
    · -- M < 0
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = -(m : ℤ) := ⟨M.natAbs, by omega⟩
      have hmpos : 1 ≤ m := by omega
      rw [Int.natAbs_neg, Int.natAbs_natCast] at hMbound
      have hm2 : (m : ℝ) ^ 2 ≤ C₁ ^ 2 * (L : ℝ) ^ d := by
        nlinarith [mul_self_le_mul_self (Nat.cast_nonneg m) hMbound, Real.sq_sqrt hVpos.le,
          Real.sqrt_nonneg ((L : ℝ) ^ d), hC1pos.le]
      obtain ⟨hc2, hb2, hc3, hb3, hcD⟩ :=
        tower_conditions_of_le d L N m hN hL hq₀ hC1cond hC1bud hMbound
      have hcoeff := towerEnergyCoeff_le d L N m hq₀ hm2
      rw [← hC2] at hcoeff
      have hsq : ((-(m : ℤ) : ℤ) : ℝ) ^ 2 = (m : ℝ) ^ 2 := by push_cast; ring
      have hmain := towerState_neg_rayleigh_bound d L N m hN hL hmpos Φ E₀ hev hmin hΦ hsing3 hsing1
        hq₀ hlro hc2 hb2 hc3 hb3 hcD htower
      rw [hsq]
      linarith [hmain, hcoeff]
    · -- M = 0
      subst hM
      have hHerm := heisenbergHamiltonianS_torus_isHermitian d L N
      have hE0im : E₀.im = 0 := hermitian_mulVec_eigenvalue_im_zero hHerm hΦ hev
      have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
        (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
      have hΦim : (star Φ ⬝ᵥ Φ).im = 0 :=
        ((Complex.le_def.mp (dotProduct_star_self_nonneg Φ)).2).symm
      rw [show towerState (torusParitySublattice d L) N (0 : ℤ) Φ = Φ from by rw [towerState]; simp,
        hev, dotProduct_smul, smul_eq_mul, Complex.mul_re, hE0im, hΦim]
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
        tower_conditions_of_le d L N m hN hL hq₀ hC1cond hC1bud hMbound
      have hcoeff := towerEnergyCoeff_le d L N m hq₀ hm2
      rw [← hC2] at hcoeff
      have hsq : ((m : ℤ) : ℝ) ^ 2 = (m : ℝ) ^ 2 := by push_cast; ring
      have hmain := towerState_pos_rayleigh_bound d L N m hN hL hmpos Φ E₀ hev hmin hΦ hsing3 hsing1
        hq₀ hlro hc2 hb2 hc3 hb3 hcD htower
      rw [hsq]
      linarith [hmain, hcoeff]

end LatticeSystem.Quantum
