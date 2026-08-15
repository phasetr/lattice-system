/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 4 — the numerator estimate.

The ★ variational bound (`tower_numerator_double_commutator_le`) reduces the trial-state energy gap
to `⟨Φ, [(ô⁻)^M, [Ĥ, (ô⁺)^M]] Φ⟩`.  This file supplies the Heisenberg-specific inputs of that
estimate — the Lemma R2 word bounds for the double commutator `d̂ = [ô⁺, [Ĥ, ô⁻]]` (`O(1/V)` per
term) and for the single commutator `[Ĥ, ô⁺]`, together with the Jacobi identity
`[[Ĥ, ô⁺], ô⁻] = −d̂` that surfaces `d̂` — and obtains the numerator bound by instantiating the
Hamiltonian-generic collection `tower_numerator_bound_of_word_bounds` with them.  The moment-factor
estimates at the numerator word lengths `2M−2` and `2M−3` are collected here for the callers of the
bound.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocalDecay
import LatticeSystem.Quantum.SpinS.AndersonTowerAssembly
import LatticeSystem.Quantum.SpinS.OrderDensityNumeratorEngine

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-- **S1 single-term bound.**  Lemma R2 applied to `d̂ = [ô⁺,[Ĥ,ô⁻]]` (which lies in the local-decay
class with `g₀ ≤ 96 d N⁴/V`): `|Re⟨Φ, ô^{wₗ} d̂ ô^{wᵣ} Φ⟩| ≤ 3 · (96 d N⁴/V) · mf(|wₗ|+|wᵣ|)`. -/
theorem orderDoubleComm_word_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl * orderDoubleComm d L N
        * orderWordProd d L N wr).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (wl.length + wr.length) := by
  have hbd := r2_split_independent d L N hN Φ hsing (q₀ := q₀) (ζ := (2 : ℝ)) (o₀ := (N : ℝ))
    hq₀ hm0 hratio (by positivity) (wl.length + wr.length) hcond hbudget wl wr
    (orderDoubleComm d L N) (orderDoubleCommAggregate d L N) rfl
    (isR2LocalUpTo_orderDoubleComm hL hN _)
  refine le_trans hbd ?_
  gcongr
  · exact momentFactor_nonneg d L N Φ _
  · exact orderDoubleCommAggregate_le hL hN

/-! ### Surfacing `d̂` via the Jacobi identity (LSp77 reordering core) -/

/-- **Jacobi identity surfacing `d̂`.**  The nested commutator `[[Ĥ, ô⁺], ô⁻]` equals
`[Ĥ, [ô⁺, ô⁻]] − [ô⁺, [Ĥ, ô⁻]] = [Ĥ, [ô⁺, ô⁻]] − d̂` — a pure ring identity.  Combined with
`[Ĥ, [ô⁺, ô⁻]] = 0` (the order commutator is `∝ Ŝ³_tot`, which commutes with `Ĥ`), this gives
`[[Ĥ, ô⁺], ô⁻] = −d̂`, the mechanism by which the Anderson-tower numerator surfaces `d̂`. -/
theorem heisenberg_order_jacobi (d L N : ℕ) [NeZero L] :
    (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      = (heisenbergHamiltonianS (torusNNCoupling d L) N
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          - (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - orderDoubleComm d L N := by
  rw [orderDoubleComm]; noncomm_ring

/-- **`Ĥ` commutes with the order commutator.**  Since `[ô⁺, ô⁻] = (2/V²) Ŝ³_tot` and `Ĥ` conserves
total `Ŝ³`, the inner commutator `[Ĥ, [ô⁺, ô⁻]]` vanishes. -/
theorem heisenberg_orderCommutator_commute (d L N : ℕ) [NeZero L] :
    heisenbergHamiltonianS (torusNNCoupling d L) N
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
      - (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * heisenbergHamiltonianS (torusNNCoupling d L) N = 0 := by
  rw [staggeredOrderDensity_commutator_eq, smul_smul, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    heisenbergHamiltonianS_commutator_totalSpinSOp3, smul_zero]

/-- **`[[Ĥ, ô⁺], ô⁻] = −d̂`.**  Combining the Jacobi identity with `[Ĥ, [ô⁺, ô⁻]] = 0`. -/
theorem heisenberg_order_nested_eq_neg_orderDoubleComm (d L N : ℕ) [NeZero L] :
    (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      = - orderDoubleComm d L N := by
  rw [heisenberg_order_jacobi, heisenberg_orderCommutator_commute, zero_sub]

/-- The moment factor at the numerator word length `2M−2` is bounded by `P_M / (2q₀)`: it equals the
even-`K` moment `P_{M-1}` (`2M−2 = 2(M−1)`), pinched by one LRO ratio step. -/
theorem momentFactor_twoM_sub_two_le (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq₀ : 0 < q₀) (hM : 1 ≤ M)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1)) :
    momentFactor d L N Φ (2 * M - 2) ≤ phatMoment d L N Φ M / (2 * q₀) := by
  rw [show 2 * M - 2 = 2 * (M - 1) from by omega, momentFactor_two_mul]
  have hr := hratio (M - 1)
  rw [show M - 1 + 1 = M from by omega] at hr
  rw [le_div_iff₀ (by linarith)]
  linarith [hr]

/-- The moment factor at the numerator word length `2M−3` is bounded by
`P_M / (2q₀) · (1 + 1/√(2q₀))`, uniformly for `M ≥ 1`.  For `M ≥ 2` one `momentFactor_succ_ge` step
lifts `√(2q₀)·mf(2M-3) ≤ mf(2M-2) ≤ P_M/(2q₀)`, giving the sharper `P_M/(2q₀)/√(2q₀)`; for `M = 1`
both word lengths collapse to `0` and `mf(0) ≤ P_1/(2q₀)`.  The single `(1 + 1/√(2q₀))` factor
covers both, so the trial bound is uniform in `M ≥ 1` (no separate `M = 1` edge case). -/
theorem momentFactor_twoM_sub_three_le (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq₀ : 0 < q₀) (hM : 1 ≤ M)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1)) :
    momentFactor d L N Φ (2 * M - 3)
      ≤ phatMoment d L N Φ M / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)) := by
  have hsqrt : 0 < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by positivity)
  have htwo := momentFactor_twoM_sub_two_le d L N M Φ hq₀ hM hratio
  have hPMnn : 0 ≤ phatMoment d L N Φ M := phatMoment_nonneg d L N Φ M
  have hdivnn : 0 ≤ phatMoment d L N Φ M / (2 * q₀) := by positivity
  have hfacnn : 0 ≤ (1 : ℝ) / Real.sqrt (2 * q₀) := by positivity
  rcases lt_or_ge M 2 with hM1 | hM2
  · interval_cases M
    have h0 : (2 * 1 - 3 : ℕ) = (2 * 1 - 2 : ℕ) := by norm_num
    rw [h0]
    nlinarith [htwo, hdivnn, hfacnn, mul_nonneg hdivnn hfacnn]
  · have hstep : Real.sqrt (2 * q₀) * momentFactor d L N Φ (2 * M - 3)
        ≤ momentFactor d L N Φ (2 * M - 2) := by
      have hsucc := momentFactor_succ_ge d L N Φ (2 * M - 3) (le_of_lt hq₀)
        (show 2 * q₀ * phatMoment d L N Φ ((2 * M - 3) / 2)
            ≤ phatMoment d L N Φ ((2 * M - 3) / 2 + 1) from by
          rw [show (2 * M - 3) / 2 = M - 2 from by omega,
            show M - 2 + 1 = M - 1 from by omega]
          have := hratio (M - 2); rwa [show M - 2 + 1 = M - 1 from by omega] at this)
      rwa [show 2 * M - 3 + 1 = 2 * M - 2 from by omega] at hsucc
    have hsharp : momentFactor d L N Φ (2 * M - 3)
        ≤ phatMoment d L N Φ M / (2 * q₀) / Real.sqrt (2 * q₀) := by
      calc momentFactor d L N Φ (2 * M - 3)
          ≤ momentFactor d L N Φ (2 * M - 2) / Real.sqrt (2 * q₀) := by
            rw [le_div_iff₀ hsqrt]; linarith [hstep]
        _ ≤ phatMoment d L N Φ M / (2 * q₀) / Real.sqrt (2 * q₀) :=
            (div_le_div_iff_of_pos_right hsqrt).mpr htwo
    calc momentFactor d L N Φ (2 * M - 3)
        ≤ phatMoment d L N Φ M / (2 * q₀) / Real.sqrt (2 * q₀) := hsharp
      _ = phatMoment d L N Φ M / (2 * q₀) * (1 / Real.sqrt (2 * q₀)) := by ring
      _ ≤ phatMoment d L N Φ M / (2 * q₀) * (1 + 1 / Real.sqrt (2 * q₀)) := by
          gcongr; linarith [hfacnn]

/-! ### S2/S3 single-term bound via R2 on `G = [Ĥ, ô⁺]` -/

/-- **S2/S3 single-term bound (R2 on `G = [Ĥ, ô⁺]`).**  Lemma R2 applied to the single
Heisenberg–order commutator (in the local-decay class with `g₀ ≤ 24 d N³`):
`|Re⟨Φ, ô^{wₗ} G ô^{wᵣ} Φ⟩| ≤ 3 · (24 d N³) · mf(|wₗ|+|wᵣ|)`. -/
theorem heisenbergRaisingComm_word_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * orderWordProd d L N wr).mulVec Φ).re|
      ≤ 3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (wl.length + wr.length) := by
  have hbd := r2_split_independent d L N hN Φ hsing (q₀ := q₀) (ζ := (2 : ℝ)) (o₀ := (N : ℝ))
    hq₀ hm0 hratio (by positivity) (wl.length + wr.length) hcond hbudget wl wr
    (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
      - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
    (heisenbergRaisingCommAggregate d L N) rfl
    (isR2LocalUpTo_heisenbergRaisingComm hL hN _)
  refine le_trans hbd ?_
  gcongr
  · exact momentFactor_nonneg d L N Φ _
  · exact heisenbergRaisingCommAggregate_le hL hN

/-! ### Assembly of the numerator bound -/

/-- **Numerator double-commutator bound.**  The ★-variational numerator
`⟨Φ, [(ô⁻)^M,[Ĥ,(ô⁺)^M]] Φ⟩` is bounded by `M²` copies of the per-insertion bound: the generic
collection `tower_numerator_bound_of_word_bounds` applied to the Heisenberg Hamiltonian, with
`d̂ = [ô⁺,[Ĥ,ô⁻]]` as the double commutator (`[[Ĥ,ô⁺],ô⁻] = −d̂`) and the two Lemma R2 word bounds
`orderDoubleComm_word_re_bound` (`c₁ = 96 d N⁴/V`) and `heisenbergRaisingComm_word_re_bound`
(`c₂ = 24 d N³`) as its hypotheses. -/
theorem tower_numerator_bound (d L N M : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ M
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N false ^ M).mulVec Φ).re|
      ≤ (M : ℝ) * ((M : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
            * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))) := by
  exact tower_numerator_bound_of_word_bounds d L N M Φ hsing
    (heisenbergHamiltonianS (torusNNCoupling d L) N) _ (orderDoubleComm d L N) rfl
    (heisenberg_order_nested_eq_neg_orderDoubleComm d L N) (by positivity)
    (fun wl wr hc hb =>
      orderDoubleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr hc hb)
    (fun wl wr hc hb =>
      heisenbergRaisingComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr hc hb)
    hcond2 hbudget2 hcond3 hbudget3

end LatticeSystem.Quantum
