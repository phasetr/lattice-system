/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 4 — the numerator estimate.

The ★ variational bound (`tower_numerator_double_commutator_le`) reduces the trial-state energy gap to
`⟨Φ, [(ô⁻)^M, [Ĥ, (ô⁺)^M]] Φ⟩`.  This file expands that double commutator via `commutator_pow_eq_sum`
and prepares to feed the pieces to Lemma R2: the `d̂ = [ô⁺, [Ĥ, ô⁻]]` terms (first sum, `O(M²/V)`) and
the `[ô⁺, ô⁻]` terms (second/third sums, `O(M⁴/V²)`).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocalDecay
import LatticeSystem.Quantum.SpinS.AndersonTowerAssembly

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-- **Commutator-power expansion of `[Ĥ, (ô⁺)^M]`.**  The inner commutator of the numerator splits
into a telescoping sum of single `[Ĥ, ô⁺]` insertions between powers of the order density. -/
theorem heisenberg_orderDensityPow_commutator_eq (d L N M : ℕ) [NeZero L] :
    heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
        - staggeredOrderDensityOpS d L N true ^ M
          * heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ j ∈ Finset.range M, staggeredOrderDensityOpS d L N true ^ j
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j) :=
  commutator_pow_eq_sum _ _ M

/-- **The numerator double commutator as a single sum over insertion positions.**  Substituting the
commutator-power expansion of `[Ĥ, (ô⁺)^M]` into the ★-variational numerator gives a sum over `j` of
the `(ô⁻)^M`-commutators of the position-`j` `[Ĥ, ô⁺]` insertions. -/
theorem numerator_eq_sum_j (d L N M : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ M
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N false ^ M
      = ∑ j ∈ Finset.range M,
          (staggeredOrderDensityOpS d L N false ^ M
              * (staggeredOrderDensityOpS d L N true ^ j
                * (heisenbergHamiltonianS (torusNNCoupling d L) N
                    * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true
                    * heisenbergHamiltonianS (torusNNCoupling d L) N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            - (staggeredOrderDensityOpS d L N true ^ j
                * (heisenbergHamiltonianS (torusNNCoupling d L) N
                    * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true
                    * heisenbergHamiltonianS (torusNNCoupling d L) N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
              * staggeredOrderDensityOpS d L N false ^ M) := by
  rw [heisenberg_orderDensityPow_commutator_eq, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]

/-- **Scalarization of an inserted `[ô⁺, ô⁻]` (S2/S3 core).**  On a total-`Ŝ³` singlet `Φ`, the
order commutator inserted between two order words collapses to a scalar (the suffix charge), since
`[ô⁺, ô⁻]` acts on any order-word state as `(V⁻² · 2 m(suf))`:
`(ô^{wₗ} [ô⁺,ô⁻] ô^{wᵣ}) Φ = (V⁻² · 2 m(wᵣ)) · (ô^{wₗ} ô^{wᵣ}) Φ`. -/
theorem orderWord_orderCommutator_insert_mulVec_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (wl wr : List Bool) :
    (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * orderWordProd d L N wr).mulVec Φ
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr))
          • (orderWordProd d L N wl * orderWordProd d L N wr).mulVec Φ := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    orderCommutator_mulVec_orderWordProd d L N Φ hsing wr, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]

/-- The identity operator lies in the local-decay class with `ζ = 0` (empty support). -/
theorem isR2LocalUpTo_one (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K 0 (N : ℝ) (manyBodyOperatorNormS (1 : ManyBodyOpS (HypercubicTorus d L) N))
      (1 : ManyBodyOpS (HypercubicTorus d L) N) := by
  have hsupp : SupportedOn (∅ : Finset (HypercubicTorus d L))
      (1 : ManyBodyOpS (HypercubicTorus d L) N) := fun z _ B => Commute.one_left _
  simpa using isR2LocalUpTo_of_supported hsupp hN K

/-- **Plain order-word expectation bound** `|Re⟨Φ, ô^{wₗ} ô^{wᵣ} Φ⟩| ≤ 3‖1‖ · mf(|wₗ|+|wᵣ|)`
(Lemma R2 with the trivial insertion `G = 1`). -/
theorem plain_orderWord_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl * orderWordProd d L N wr).mulVec Φ).re|
      ≤ 3 * manyBodyOperatorNormS (1 : ManyBodyOpS (HypercubicTorus d L) N)
          * momentFactor d L N Φ (wl.length + wr.length) := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hbd := r2_split_independent d L N hN Φ hsing (q₀ := q₀) (ζ := (0 : ℝ)) (o₀ := (N : ℝ))
    hq₀ hm0 hratio (by simp) (wl.length + wr.length) hcond (by simp) wl wr 1
    (manyBodyOperatorNormS 1) rfl (isR2LocalUpTo_one d L N hN _)
  rwa [mul_one] at hbd

/-- **S2/S3 single-term bound.**  Combining the `[ô⁺,ô⁻]` scalarization with the plain order-word R2
bound: `|Re⟨Φ, ô^{wₗ} [ô⁺,ô⁻] ô^{wᵣ} Φ⟩| ≤ ‖V⁻² · 2 m(wᵣ)‖ · 3‖1‖ · mf(|wₗ|+|wᵣ|)`. -/
theorem orderCommutator_word_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * orderWordProd d L N wr).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr)‖
        * (3 * manyBodyOperatorNormS (1 : ManyBodyOpS (HypercubicTorus d L) N)
            * momentFactor d L N Φ (wl.length + wr.length)) := by
  rw [orderWord_orderCommutator_insert_mulVec_eq d L N Φ hsing wl wr, dotProduct_smul,
    smul_eq_mul]
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr) with hs
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl * orderWordProd d L N wr).mulVec Φ with hZ
  have hsim : s.im = 0 := by
    rw [hs]; simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im]
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [hre, abs_mul]
  refine mul_le_mul ?_ (plain_orderWord_re_bound d L N hN Φ hsing hq₀ hm0 hratio wl wr hcond)
    (abs_nonneg _) (norm_nonneg _)
  simpa using RCLike.abs_re_le_norm s

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

end LatticeSystem.Quantum
