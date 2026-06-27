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

/-! ### Hamiltonian elimination on the ground eigenvector (assembly helpers) -/

/-- **Right `Ĥ`-elimination.**  When `Ĥ Φ = E₀ Φ`, an `Ĥ` factored on the right of an operator
collapses to the scalar `E₀`: `⟨Φ, (X Ĥ) Φ⟩ = E₀ ⟨Φ, X Φ⟩`. -/
theorem heisenberg_dotProduct_right (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
    (hev : (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ)
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    star Φ ⬝ᵥ (X * heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ
      = E₀ * (star Φ ⬝ᵥ X.mulVec Φ) := by
  rw [← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- **Left `Ĥ`-elimination.**  For Hermitian `Ĥ` with `Ĥ Φ = E₀ Φ`, an `Ĥ` factored on the left
collapses to `conj E₀`: `⟨Φ, (Ĥ X) Φ⟩ = conj(E₀) ⟨Φ, X Φ⟩`. -/
theorem heisenberg_dotProduct_left (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
    (hev : (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ)
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    star Φ ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N * X).mulVec Φ
      = (starRingEnd ℂ) E₀ * (star Φ ⬝ᵥ X.mulVec Φ) := by
  rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
    (heisenbergHamiltonianS_torus_isHermitian d L N).eq, hev, star_smul, smul_dotProduct,
    smul_eq_mul]
  rfl

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

/-- **Operator Leibniz rule for commutators.**  `[X·Y, Z] = X·[Y, Z] + [X, Z]·Y`. -/
theorem commutator_mul_left_eq {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (X Y Z : ManyBodyOpS Λ N) :
    X * Y * Z - Z * (X * Y) = X * (Y * Z - Z * Y) + (X * Z - Z * X) * Y := by
  noncomm_ring

/-- **Anti-expansion of `(ô⁻)^M` against an operator.**  `(ô⁻)^M X − X (ô⁻)^M` telescopes into a
signed sum of single `[X, ô⁻]` insertions between powers of `ô⁻`. -/
theorem orderMinusPow_commutator_eq (d L N M : ℕ) [NeZero L]
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ M * X
        - X * staggeredOrderDensityOpS d L N false ^ M
      = - ∑ k ∈ Finset.range M, staggeredOrderDensityOpS d L N false ^ k
          * (X * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * X)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [← neg_sub (X * staggeredOrderDensityOpS d L N false ^ M)
      (staggeredOrderDensityOpS d L N false ^ M * X), commutator_pow_eq_sum]

/-- A power of a single order density is the order-word product over a constant word:
`(ô^b)^a = ô^{replicate a b}`.  Lets the numerator's order-density powers be fed to the R2-based
single-term bounds, which are phrased over `orderWordProd`. -/
theorem orderWordProd_replicate (d L N a : ℕ) [NeZero L] (b : Bool) :
    orderWordProd d L N (List.replicate a b) = staggeredOrderDensityOpS d L N b ^ a := by
  rw [orderWordProd, List.map_replicate, List.prod_replicate]

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

/-- The moment factor at the numerator word length `2M−3` is bounded by `P_M / (2q₀) / √(2q₀)`:
one `momentFactor_succ_ge` step lifts `√(2q₀)·mf(2M-3) ≤ mf(2M-2)`, then
`momentFactor_twoM_sub_two_le` bounds `mf(2M-2) ≤ P_M/(2q₀)`. -/
theorem momentFactor_twoM_sub_three_le (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq₀ : 0 < q₀) (hM : 2 ≤ M)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1)) :
    momentFactor d L N Φ (2 * M - 3)
      ≤ phatMoment d L N Φ M / (2 * q₀) / Real.sqrt (2 * q₀) := by
  have hsqrt : 0 < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by positivity)
  have hstep : Real.sqrt (2 * q₀) * momentFactor d L N Φ (2 * M - 3)
      ≤ momentFactor d L N Φ (2 * M - 2) := by
    have hsucc := momentFactor_succ_ge d L N Φ (2 * M - 3) (le_of_lt hq₀)
      (show 2 * q₀ * phatMoment d L N Φ ((2 * M - 3) / 2)
          ≤ phatMoment d L N Φ ((2 * M - 3) / 2 + 1) from by
        rw [show (2 * M - 3) / 2 = M - 2 from by omega,
          show M - 2 + 1 = M - 1 from by omega]
        have := hratio (M - 2); rwa [show M - 2 + 1 = M - 1 from by omega] at this)
    rwa [show 2 * M - 3 + 1 = 2 * M - 2 from by omega] at hsucc
  have htwo := momentFactor_twoM_sub_two_le d L N M Φ hq₀ (by omega) hratio
  calc momentFactor d L N Φ (2 * M - 3)
      ≤ momentFactor d L N Φ (2 * M - 2) / Real.sqrt (2 * q₀) := by
        rw [le_div_iff₀ hsqrt]; linarith [hstep]
    _ ≤ phatMoment d L N Φ M / (2 * q₀) / Real.sqrt (2 * q₀) :=
        (div_le_div_iff_of_pos_right hsqrt).mpr htwo

/-- **Triple Leibniz decomposition.**  `[A·G·C, Z] = A·G·[C,Z] + A·[G,Z]·C + [A,Z]·G·C` (pure ring
identity).  Applied with `A = (ô⁺)^j`, `G = [Ĥ,ô⁺]`, `C = (ô⁺)^{M-1-j}`, `Z = ô⁻`: the middle term's
`[G,Z] = [[Ĥ,ô⁺],ô⁻] = −d̂` gives the S1 contribution, the outer two give the S2/S3 crossings. -/
theorem mul_mul_commutator_decomp {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A G C Z : ManyBodyOpS Λ N) :
    A * G * C * Z - Z * (A * G * C)
      = A * G * (C * Z - Z * C) + A * (G * Z - Z * G) * C + (A * Z - Z * A) * G * C := by
  noncomm_ring

/-- **S1 single-term bound (powers form).**  Each `(ô⁻)^k (ô⁺)^j d̂ (ô⁺)^{M-1-j} (ô⁻)^{M-1-k}`
expectation is an order-word sandwich of `d̂` of total length `2M−2`, hence bounded by
`3(96dN⁴/V)·mf(2M−2)` via `orderDoubleComm_word_re_bound`. -/
theorem s1_term_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * orderDoubleComm d L N
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (2 * M - 2) := by
  set wl := List.replicate k false ++ List.replicate j true with hwldef
  set wr := List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false with hwrdef
  have hwl : orderWordProd d L N wl = staggeredOrderDensityOpS d L N false ^ k
      * staggeredOrderDensityOpS d L N true ^ j := by
    rw [hwldef, orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate]
  have hwr : orderWordProd d L N wr = staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
      * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
    rw [hwrdef, orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate]
  have hlen : wl.length + wr.length = 2 * M - 2 := by
    simp only [hwldef, hwrdef, List.length_append, List.length_replicate]; omega
  have hop : staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * orderDoubleComm d L N
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N wl * orderDoubleComm d L N * orderWordProd d L N wr := by
    rw [hwl, hwr]; noncomm_ring
  rw [hop]
  have hbd := orderDoubleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)
  rwa [hlen] at hbd

/-! ### S2/S3 single-term bound via R2 on `G = [Ĥ, ô⁺]` -/

/-- **Scalarization of an inserted `[ô⁺,ô⁻]` with a left factor.**  Generalizes
`orderWord_orderCommutator_insert_mulVec_eq` to allow an arbitrary operator `X` to the left:
`(X · ô^{wₗ} [ô⁺,ô⁻] ô^{wᵣ}) Φ = (V⁻²·2 m(wᵣ)) · (X · ô^{wₗ} ô^{wᵣ}) Φ`. -/
theorem orderCommutator_insert_left_mulVec_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (X : ManyBodyOpS (HypercubicTorus d L) N) (wl wr : List Bool) :
    (X * (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * orderWordProd d L N wr)).mulVec Φ
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr))
          • (X * (orderWordProd d L N wl * orderWordProd d L N wr)).mulVec Φ := by
  rw [← Matrix.mulVec_mulVec, orderWord_orderCommutator_insert_mulVec_eq d L N Φ hsing wl wr,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]

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

/-- **S2/S3 term-1 leaf.**  A term with `G = [Ĥ, ô⁺]` left of a Φ-side `[ô⁺,ô⁻]`: scalarize the
order commutator (left-factor form), then bound the residual `G`-sandwich by R2:
`|Re⟨Φ, ô^{wₗ} G ô^{wₘ} [ô⁺,ô⁻] ô^{wᵣ} Φ⟩| ≤ ‖V⁻²·2m(wᵣ)‖ · 3(24dN³) · mf(|wₗ|+|wₘ|+|wᵣ|)`. -/
theorem s23_term1_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + (wm.length + wr.length) : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + (wm.length + wr.length) : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (orderWordProd d L N wm
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr)‖
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
            * momentFactor d L N Φ (wl.length + (wm.length + wr.length))) := by
  rw [orderCommutator_insert_left_mulVec_eq d L N Φ hsing
      (orderWordProd d L N wl
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true
            * heisenbergHamiltonianS (torusNNCoupling d L) N)) wm wr,
    dotProduct_smul, smul_eq_mul]
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr) with hs
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have hsim : s.im = 0 := by rw [hs]; simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im]
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl
      * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
        - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
      * (orderWordProd d L N wm * orderWordProd d L N wr)).mulVec Φ with hZ
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [hre, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · simpa using RCLike.abs_re_le_norm s
  · rw [hZ, ← orderWordProd_mul_append]
    have h := heisenbergRaisingComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl (wm ++ wr)
      (by rw [List.length_append]; exact hcond) (by rw [List.length_append]; exact hbudget)
    simpa only [List.length_append] using h

/-- **Bra-side scalarization of a buried `Ŝ³`.**  Moving `Ŝ³` (`= [ô⁺,ô⁻]·V²/2`) onto the bra `Φ`
via Hermiticity: `(ô^{wₗ})†Φ` is an `Ŝ³` eigenstate (charge `m((wₗ)ʳ⁻)`), so
`⟨Φ, ô^{wₗ} Ŝ³ X Φ⟩ = conj(m((wₗ)ʳ⁻)) ⟨Φ, ô^{wₗ} X Φ⟩` for any right factor `X`. -/
theorem dotProduct_orderWord_totalSpinSOp3_mid_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (wl : List Bool)
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    star Φ ⬝ᵥ (orderWordProd d L N wl * totalSpinSOp3 (HypercubicTorus d L) N * X).mulVec Φ
      = (starRingEnd ℂ) (mCharge (wl.reverse.map not))
          * (star Φ ⬝ᵥ (orderWordProd d L N wl * X).mulVec Φ) := by
  have key : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((orderWordProd d L N (wl.reverse.map not)).mulVec Φ)
      = mCharge (wl.reverse.map not) • (orderWordProd d L N (wl.reverse.map not)).mulVec Φ :=
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N _ hsing
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    star_dotProduct_mulVec_conjTranspose (orderWordProd d L N wl), orderWordProd_conjTranspose,
    star_dotProduct_mulVec_conjTranspose (totalSpinSOp3 (HypercubicTorus d L) N),
    (totalSpinSOp3_isHermitian (HypercubicTorus d L) N).eq, key, star_smul, smul_dotProduct,
    smul_eq_mul, ← orderWordProd_conjTranspose,
    ← star_dotProduct_mulVec_conjTranspose, Matrix.mulVec_mulVec, starRingEnd_apply]

/-- **S2/S3 term-3 leaf.**  `[ô⁺,ô⁻]` left of `G = [Ĥ,ô⁺]`: convert to `(2/V²)Ŝ³`, scalarize `Ŝ³`
onto the bra (`dotProduct_orderWord_totalSpinSOp3_mid_eq`), then bound the residual `G`-sandwich by
R2 — giving `‖(2/V²) conj(m((wₗ)ʳ⁻))‖ · 3(24dN³) · mf`. -/
theorem s23_term3_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * (((wl ++ wm).length + wr.length : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : (((wl ++ wm).length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N wm
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2) * (starRingEnd ℂ) (mCharge (wl.reverse.map not))‖
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
            * momentFactor d L N Φ ((wl ++ wm).length + wr.length)) := by
  set Y := orderWordProd d L N wm
    * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
      - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
    * orderWordProd d L N wr with hY
  rw [staggeredOrderDensity_commutator_eq, smul_smul, mul_smul_comm, smul_mul_assoc,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_orderWord_totalSpinSOp3_mid_eq d L N Φ hsing wl Y]
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2)
    * (starRingEnd ℂ) (mCharge (wl.reverse.map not)) with hs
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have hsim : s.im = 0 := by
    rw [hs]
    simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im, Complex.conj_im, Complex.conj_re]
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl * Y).mulVec Φ with hZ
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [← mul_assoc, ← hs, hre, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · simpa using RCLike.abs_re_le_norm s
  · rw [hZ, hY]
    convert heisenbergRaisingComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio (wl ++ wm) wr
      hcond hbudget using 4
    rw [orderWordProd_mul_append]; noncomm_ring

/-! ### Collection helpers (nested-sum triangle inequality) -/

/-- **Right power commutator telescope.**  `A^r·B − B·A^r = ∑_l A^l (A·B−B·A) A^{r-1-l}`. -/
theorem pow_right_commutator_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (r : ℕ) :
    A ^ r * B - B * A ^ r
      = ∑ l ∈ Finset.range r, A ^ l * (A * B - B * A) * A ^ (r - 1 - l) := by
  have h : B * A ^ r - A ^ r * B
      = ∑ l ∈ Finset.range r, A ^ l * (B * A - A * B) * A ^ (r - 1 - l) :=
    commutator_pow_eq_sum B A r
  have key : (∑ l ∈ Finset.range r, A ^ l * (A * B - B * A) * A ^ (r - 1 - l))
      = -(∑ l ∈ Finset.range r, A ^ l * (B * A - A * B) * A ^ (r - 1 - l)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)
  rw [key, ← h]; abel

/-- **Triangle inequality for a sum of sandwiched expectations.**  The real part of a finite-sum
operator's expectation is bounded by the sum of the per-term absolute real parts. -/
theorem abs_re_dotProduct_sum_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → ManyBodyOpS (HypercubicTorus d L) N) :
    |(star Φ ⬝ᵥ (∑ i ∈ s, f i).mulVec Φ).re| ≤ ∑ i ∈ s, |(star Φ ⬝ᵥ (f i).mulVec Φ).re| := by
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.abs_sum_le_sum_abs (fun i => (star Φ ⬝ᵥ (f i).mulVec Φ).re) s

/-- The same triangle bound for a negated finite sum (`|Re| = |Re of the un-negated sum|`). -/
theorem abs_re_dotProduct_neg_sum_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → ManyBodyOpS (HypercubicTorus d L) N) :
    |(star Φ ⬝ᵥ (- ∑ i ∈ s, f i).mulVec Φ).re| ≤ ∑ i ∈ s, |(star Φ ⬝ᵥ (f i).mulVec Φ).re| := by
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, abs_neg]
  exact abs_re_dotProduct_sum_le d L N Φ s f

/-- **Per-`j` three-way split with `d̂` surfaced.**  `[Tⱼ, ô⁻]` splits as `(ô⁺)^j G [(ô⁺)^r,ô⁻]`
(S2) `− (ô⁺)^j d̂ (ô⁺)^r` (S1) `+ [(ô⁺)^j,ô⁻] G (ô⁺)^r` (S3), where `Tⱼ = (ô⁺)^j G (ô⁺)^r`,
`G = [Ĥ,ô⁺]`, `r = M-1-j`, via the triple Leibniz plus the Jacobi identity `[G, ô⁻] = −d̂`. -/
theorem Tj_orderMinus_decomp (d L N j r : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N true ^ r) * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false * (staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N true ^ r)
      = staggeredOrderDensityOpS d L N true ^ j
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r)
        + staggeredOrderDensityOpS d L N true ^ j * (- orderDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ r
        + (staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ r := by
  rw [mul_mul_commutator_decomp, heisenberg_order_nested_eq_neg_orderDoubleComm]

/-- **S1 middle-term bound (sandwiched).**  The middle `(ô⁺)^j(−d̂)(ô⁺)^{M-1-j}`, sandwiched by
`(ô⁻)^k … (ô⁻)^{M-1-k}`, equals `−` the `s1_term_bound` operator, so it has the same
`3(96dN⁴/V)·mf(2M-2)` bound. -/
theorem s1_middle_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (- orderDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (2 * M - 2) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (- orderDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = - (staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j * orderDoubleComm d L N
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)) from by noncomm_ring,
    Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, abs_neg]
  exact s1_term_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond hbudget

/-- A per-`l` S2 term equals an `s23_term1_bound`-shaped operator (replicate words). -/
theorem s2_lterm_eq (d L N j k l r : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k * staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate j true)
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (orderWordProd d L N (List.replicate l true)
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N (List.replicate (r - 1 - l) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- The order-commutator scalar coefficient is bounded by the word length:
`‖V⁻²·2·m(w)‖ ≤ V⁻²·2·|w|`. -/
theorem orderScalar_norm_le (d L : ℕ) [NeZero L] (w : List Bool) :
    ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge w)‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (w.length : ℝ)) := by
  rw [norm_mul, show ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹‖
      = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ from by
    simp only [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left (mCharge_norm_le w) (by norm_num)

/-- A per-`l` S3 term equals an `s23_term3_bound`-shaped operator (replicate words). -/
theorem s3_lterm_eq (d L N j k l : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate l true)
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N (List.replicate (j - 1 - l) true)
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * orderWordProd d L N (List.replicate (M - 1 - j) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- **Per-`l` S2 bound (uniform in `l`).**  Each S2 term `≤ V⁻²·2·(2M)·3(24dN³)·mf(2M-3)`,
independent of `l`, via `s2_lterm_eq` → `s23_term1_bound` → `orderScalar_norm_le`. -/
theorem s2_lterm_bound (d L N M j k l : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M) (hl : l < M - 1 - j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k * staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)) := by
  have hwrlen : (List.replicate (M - 1 - j - 1 - l) true
      ++ List.replicate (M - 1 - k) false).length ≤ 2 * M := by
    simp only [List.length_append, List.length_replicate]; omega
  have hlen : (List.replicate k false ++ List.replicate j true).length
      + ((List.replicate l true).length
        + (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false).length)
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [s2_lterm_eq d L N j k l (M - 1 - j)]
  refine le_trans (s23_term1_bound d L N hN hL Φ hsing hq₀ hm0 hratio
    (List.replicate k false ++ List.replicate j true) (List.replicate l true)
    (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _))
  refine (orderScalar_norm_le d L _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hwrlen) (by norm_num)

/-- **Per-`l` S3 bound (uniform in `l`).**  Each S3 term `≤ V⁻²·2·(2M)·3(24dN³)·mf(2M-3)`,
independent of `l`, via `s3_lterm_eq` → `s23_term3_bound` → the conjugate scalar bound. -/
theorem s3_lterm_bound (d L N M j k l : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M) (hl : l < j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)) := by
  have hlen : ((List.replicate k false ++ List.replicate l true)
        ++ List.replicate (j - 1 - l) true).length
      + (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false).length
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [s3_lterm_eq d L N j k l]
  refine le_trans (s23_term3_bound d L N hN hL Φ hsing hq₀ hm0 hratio
    (List.replicate k false ++ List.replicate l true) (List.replicate (j - 1 - l) true)
    (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _))
  rw [norm_mul, Complex.norm_conj,
    show ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2‖
      = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * 2 from by
      simp only [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_two]]
  have hm : ‖mCharge ((List.replicate k false ++ List.replicate l true).reverse.map not)‖
      ≤ 2 * (M : ℝ) := by
    refine (mCharge_norm_le _).trans ?_
    rw [List.length_map, List.length_reverse, List.length_append, List.length_replicate,
      List.length_replicate]
    exact_mod_cast (by omega : k + l ≤ 2 * M)
  have hV : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ := by positivity
  nlinarith [hm, hV, norm_nonneg (mCharge ((List.replicate k false
    ++ List.replicate l true).reverse.map not)),
    mul_le_mul_of_nonneg_left hm hV]

/-- The sandwiched S2 part is the `l`-sum of the per-`l` S2 operators (expand `[(ô⁺)^r,ô⁻]`). -/
theorem s2_part_eq (d L N j k r : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range r, staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [pow_right_commutator_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **S2 part bound.**  The sandwiched S2 part is `≤ M · (V⁻²·2·(2M)·3(24dN³)·mf(2M-3))`
(`≤ M` terms, each by `s2_lterm_bound`). -/
theorem s2_part_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j) * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3))) := by
  rw [s2_part_eq d L N j k (M - 1 - j)]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => s2_lterm_bound d L N M j k l hN hL Φ hsing hq₀ hm0
    hratio hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : M - 1 - j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _)))

/-- **S3 part operator identity.**  The sandwiched S3 part
`(ô⁻)^k·([(ô⁺)^j,ô⁻]·G·(ô⁺)^{M-1-j})·(ô⁻)^{M-1-k}` expands (left commutator
`pow_right_commutator_eq_sum` over `l<j`) into the per-`l` S3 operators that `s3_lterm_bound`
bounds. -/
theorem s3_part_eq (d L N j k : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range j, staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [pow_right_commutator_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **S3 part bound.**  The sandwiched S3 part is `≤ M · (V⁻²·2·(2M)·3(24dN³)·mf(2M-3))`
(`≤ M` terms, each by `s3_lterm_bound`). -/
theorem s3_part_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3))) := by
  rw [s3_part_eq d L N j k]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => s3_lterm_bound d L N M j k l hN hL Φ hsing hq₀ hm0
    hratio hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _)))

/-- **Per-`(j,k)` term bound.**  The sandwiched commutator
`(ô⁻)^k·([T_j, ô⁻])·(ô⁻)^{M-1-k}` (with `T_j = (ô⁺)^j·G·(ô⁺)^{M-1-j}`) decomposes
(`Tj_orderMinus_decomp`) into the S1 middle `(−d̂)`, the S2 source and the S3 source; the triangle
inequality plus `s1_middle_bound`, `s2_part_bound`, `s3_part_bound` yields the total bound. -/
theorem tower_jk_term_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ j * (- orderDoubleComm d L N)
            * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
        + (staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
            * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
              - staggeredOrderDensityOpS d L N true
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
            * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
                * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
          + staggeredOrderDensityOpS d L N false ^ k
            * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k))
      from by rw [Tj_orderMinus_decomp d L N j (M - 1 - j)]; noncomm_ring,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    Complex.add_re, Complex.add_re]
  refine (abs_add_le _ _).trans (add_le_add ?_ ((abs_add_le _ _).trans (add_le_add ?_ ?_)))
  · exact s1_middle_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond2 hbudget2
  · exact s2_part_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond3 hbudget3
  · exact s3_part_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond3 hbudget3

/-- **Numerator double-commutator bound.**  Summing the per-`(j,k)` bound over the `M²` insertion
positions (`numerator_eq_sum_j` over `j`, then `orderMinusPow_commutator_eq` over `k`, with the
nested triangle inequality) bounds the ★-variational numerator
`⟨Φ, [(ô⁻)^M,[Ĥ,(ô⁺)^M]] Φ⟩` by `M²` copies of the per-`(j,k)` bound. -/
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
  rw [numerator_eq_sum_j]
  refine (abs_re_dotProduct_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    ((M : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))) ?_)
    (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro j hj
  rw [orderMinusPow_commutator_eq]
  refine (abs_re_dotProduct_neg_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
      + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
        + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))
    ?_) (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro k hk
  exact tower_jk_term_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio
    (Finset.mem_range.mp hj) (Finset.mem_range.mp hk) hcond2 hbudget2 hcond3 hbudget3

end LatticeSystem.Quantum
