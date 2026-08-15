/-
Hamiltonian-generic collection of the order-density tower numerator.

The tower numerator estimates bound `⟨Φ, [(ô⁻)^M, [Ĥ, (ô⁺)^M]] Φ⟩` by one fixed combinatorial
route: telescope the power commutator into `M` single `[Ĥ, ô⁺]` insertions, split each insertion
against `(ô⁻)^M` with the triple Leibniz rule into the `d̂`-term (S1) and the two `[ô^a, ô⁻]`
crossings (S2/S3), scalarize the crossings on the total-`Ŝ³` singlet, and collect everything with
triangle inequalities.  Only two facts about the Hamiltonian enter the route, and here they enter as
hypotheses: the single commutator `G = [Ĥ, ô⁺]` and the double commutator `D = d̂` satisfy
order-word expectation bounds (Lemma R2), and the nested commutator satisfies `[G, ô⁻] = −D`.

`tower_numerator_bound_of_word_bounds` states the collection over that interface.  The Heisenberg
numerator of Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer
2020), §4.2.2 Theorem 4.6 and the `Ĥ_ZZ` numerator of §5.3 Theorem 5.2 instantiate it with their own
Hamiltonian, single commutator and double commutator.

The algebraic primitives (scalarization, power telescopes, expectation triangle inequalities) come
from `OrderDensityNumeratorCore`; the moment factor and the order-word product from
`AndersonTowerR2Centering`.
-/
import LatticeSystem.Quantum.SpinS.OrderDensityNumeratorCore
import LatticeSystem.Quantum.SpinS.AndersonTowerR2Centering

namespace LatticeSystem.Quantum

open Matrix

/-! ### Power expansion of the numerator -/

/-- **The numerator double commutator as a single sum over insertion positions.**  Telescoping
`[Ĥ, (ô⁺)^M]` into `M` insertions of the single commutator `G = [Ĥ, ô⁺]` turns the numerator into a
sum over the insertion position `j` of the `(ô⁻)^M`-commutators of `(ô⁺)^j G (ô⁺)^{M-1-j}`. -/
private theorem orderNumerator_eq_sum_j (d L N M : ℕ) [NeZero L]
    (H G : ManyBodyOpS (HypercubicTorus d L) N)
    (hG : H * staggeredOrderDensityOpS d L N true
        - staggeredOrderDensityOpS d L N true * H = G) :
    staggeredOrderDensityOpS d L N false ^ M
        * (H * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * H)
      - (H * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * H)
        * staggeredOrderDensityOpS d L N false ^ M
      = ∑ j ∈ Finset.range M,
          (staggeredOrderDensityOpS d L N false ^ M
              * (staggeredOrderDensityOpS d L N true ^ j * G
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            - (staggeredOrderDensityOpS d L N true ^ j * G
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
              * staggeredOrderDensityOpS d L N false ^ M) := by
  have hpow : H * staggeredOrderDensityOpS d L N true ^ M
        - staggeredOrderDensityOpS d L N true ^ M * H
      = ∑ j ∈ Finset.range M, staggeredOrderDensityOpS d L N true ^ j * G
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j) := by
    rw [← hG]; exact commutator_pow_eq_sum _ _ M
  rw [hpow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-! ### Single-term bounds from the two word hypotheses -/

/-- **S1 single-term bound (powers form).**  Each `(ô⁻)^k (ô⁺)^j D (ô⁺)^{M-1-j} (ô⁻)^{M-1-k}`
expectation is an order-word sandwich of `D` of total length `2M−2`, so the word bound for `D`
applies at that length. -/
private theorem orderNumerator_s1_term_bound (d L N M j k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (D : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₁ : ℝ}
    (hD : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * D * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₁ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * D
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * c₁ * momentFactor d L N Φ (2 * M - 2) := by
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
        * staggeredOrderDensityOpS d L N true ^ j * D
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N wl * D * orderWordProd d L N wr := by
    rw [hwl, hwr]; noncomm_ring
  rw [hop]
  have hbd := hD wl wr (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)
  rwa [hlen] at hbd

/-- **S2/S3 term-1 leaf.**  With `G` left of a Φ-side `[ô⁺,ô⁻]`, scalarize the order commutator
(left-factor form) and bound the residual `G`-sandwich by the word bound for `G`. -/
private theorem orderNumerator_s23_term1_bound (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ}
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + (wm.length + wr.length) : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + (wm.length + wr.length) : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl * G
        * (orderWordProd d L N wm
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr)‖
        * (3 * c₂ * momentFactor d L N Φ (wl.length + (wm.length + wr.length))) := by
  rw [orderCommutator_insert_left_mulVec_eq d L N Φ hsing (orderWordProd d L N wl * G) wm wr,
    dotProduct_smul, smul_eq_mul]
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr) with hs
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have hsim : s.im = 0 := by rw [hs]; simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im]
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl * G
      * (orderWordProd d L N wm * orderWordProd d L N wr)).mulVec Φ with hZ
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [hre, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · simpa using RCLike.abs_re_le_norm s
  · rw [hZ, ← orderWordProd_mul_append]
    have h := hGw wl (wm ++ wr) (by rw [List.length_append]; exact hcond)
      (by rw [List.length_append]; exact hbudget)
    simpa only [List.length_append] using h

/-- **S2/S3 term-3 leaf.**  With `[ô⁺,ô⁻]` left of `G`, convert the order commutator to `(2/V²)Ŝ³`,
scalarize `Ŝ³` onto the bra, and bound the residual `G`-sandwich by the word bound for `G`. -/
private theorem orderNumerator_s23_term3_bound (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ}
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * (((wl ++ wm).length + wr.length : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : (((wl ++ wm).length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N wm * G * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2) * (starRingEnd ℂ) (mCharge (wl.reverse.map not))‖
        * (3 * c₂ * momentFactor d L N Φ ((wl ++ wm).length + wr.length)) := by
  set Y := orderWordProd d L N wm * G * orderWordProd d L N wr with hY
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
    convert hGw (wl ++ wm) wr hcond hbudget using 4
    rw [orderWordProd_mul_append]; noncomm_ring

/-! ### Per-`j` term decomposition -/

/-- **Per-`j` three-way split with `D` surfaced.**  `[(ô⁺)^j G (ô⁺)^r, ô⁻]` splits as
`(ô⁺)^j G [(ô⁺)^r, ô⁻]` (S2) `− (ô⁺)^j D (ô⁺)^r` (S1) `+ [(ô⁺)^j, ô⁻] G (ô⁺)^r` (S3), via the
triple Leibniz rule together with the nested-commutator hypothesis `[G, ô⁻] = −D`. -/
private theorem orderNumerator_Tj_decomp (d L N j r : ℕ) [NeZero L]
    (G D : ManyBodyOpS (HypercubicTorus d L) N)
    (hnest : G * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * G = -D) :
    (staggeredOrderDensityOpS d L N true ^ j * G * staggeredOrderDensityOpS d L N true ^ r)
        * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false
        * (staggeredOrderDensityOpS d L N true ^ j * G
          * staggeredOrderDensityOpS d L N true ^ r)
      = staggeredOrderDensityOpS d L N true ^ j * G
          * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r)
        + staggeredOrderDensityOpS d L N true ^ j * (-D)
          * staggeredOrderDensityOpS d L N true ^ r
        + (staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * G * staggeredOrderDensityOpS d L N true ^ r := by
  rw [mul_mul_commutator_decomp, hnest]

/-- **S1 middle-term bound (sandwiched).**  The middle `(ô⁺)^j(−D)(ô⁺)^{M-1-j}`, sandwiched by
`(ô⁻)^k … (ô⁻)^{M-1-k}`, is the negative of the S1 single-term operator, hence obeys the same
bound. -/
private theorem orderNumerator_s1_middle_bound (d L N M j k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (D : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₁ : ℝ}
    (hD : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * D * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₁ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (-D)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * c₁ * momentFactor d L N Φ (2 * M - 2) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (-D)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = - (staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j * D
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)) from by noncomm_ring,
    Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, abs_neg]
  exact orderNumerator_s1_term_bound d L N M j k Φ D hD hj hk hcond hbudget

/-! ### The S2 and S3 crossing parts -/

/-- A per-`l` S2 term equals an `orderNumerator_s23_term1_bound`-shaped operator (replicate
words). -/
private theorem orderNumerator_s2_lterm_eq (d L N M j k l r : ℕ) [NeZero L]
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ k * staggeredOrderDensityOpS d L N true ^ j * G
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate j true) * G
        * (orderWordProd d L N (List.replicate l true)
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N (List.replicate (r - 1 - l) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- A per-`l` S3 term equals an `orderNumerator_s23_term3_bound`-shaped operator (replicate
words). -/
private theorem orderNumerator_s3_lterm_eq (d L N M j k l : ℕ) [NeZero L]
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate l true)
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N (List.replicate (j - 1 - l) true) * G
          * orderWordProd d L N (List.replicate (M - 1 - j) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- **Per-`l` S2 bound (uniform in `l`).**  Each S2 term is bounded by
`V⁻²·2·(2M)·3c₂·mf(2M-3)`, independently of `l`, by rewriting it into term-1 shape and bounding the
scalarized order-commutator coefficient by the word length. -/
private theorem orderNumerator_s2_lterm_bound (d L N M j k l : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M) (hl : l < M - 1 - j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * G
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)) := by
  have hwrlen : (List.replicate (M - 1 - j - 1 - l) true
      ++ List.replicate (M - 1 - k) false).length ≤ 2 * M := by
    simp only [List.length_append, List.length_replicate]; omega
  have hlen : (List.replicate k false ++ List.replicate j true).length
      + ((List.replicate l true).length
        + (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false).length)
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [orderNumerator_s2_lterm_eq d L N M j k l (M - 1 - j) G]
  refine le_trans (orderNumerator_s23_term1_bound d L N Φ hsing G hGw
    (List.replicate k false ++ List.replicate j true) (List.replicate l true)
    (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by linarith [hc₂]) (momentFactor_nonneg d L N Φ _))
  refine (orderScalar_norm_le d L _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hwrlen) (by norm_num)

/-- **Per-`l` S3 bound (uniform in `l`).**  Each S3 term is bounded by
`V⁻²·2·(2M)·3c₂·mf(2M-3)`, independently of `l`, by rewriting it into term-3 shape and bounding the
conjugate charge coefficient by the word length. -/
private theorem orderNumerator_s3_lterm_bound (d L N M j k l : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M) (hl : l < j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)) := by
  have hlen : ((List.replicate k false ++ List.replicate l true)
        ++ List.replicate (j - 1 - l) true).length
      + (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false).length
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [orderNumerator_s3_lterm_eq d L N M j k l G]
  refine le_trans (orderNumerator_s23_term3_bound d L N Φ hsing G hGw
    (List.replicate k false ++ List.replicate l true) (List.replicate (j - 1 - l) true)
    (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by linarith [hc₂]) (momentFactor_nonneg d L N Φ _))
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

/-- The sandwiched S2 part is the `l`-sum of the per-`l` S2 operators (expand `[(ô⁺)^r, ô⁻]`). -/
private theorem orderNumerator_s2_part_eq (d L N M j k r : ℕ) [NeZero L]
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j * G
        * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range r, staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j * G
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [commutator_pow_eq_sum', Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **S2 part bound.**  The sandwiched S2 part is bounded by `M` copies of the per-`l` S2 bound. -/
private theorem orderNumerator_s2_part_bound (d L N M j k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * G
          * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
              * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * c₂ * momentFactor d L N Φ (2 * M - 3))) := by
  rw [orderNumerator_s2_part_eq d L N M j k (M - 1 - j) G]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => orderNumerator_s2_lterm_bound d L N M j k l Φ
    hsing G hc₂ hGw hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : M - 1 - j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by linarith [hc₂]) (momentFactor_nonneg d L N Φ _)))

/-- **S3 part operator identity.**  The sandwiched S3 part expands (left commutator telescope over
`l < j`) into the per-`l` S3 operators. -/
private theorem orderNumerator_s3_part_eq (d L N M j k : ℕ) [NeZero L]
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range j, staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
          * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [commutator_pow_eq_sum']
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **S3 part bound.**  The sandwiched S3 part is bounded by `M` copies of the per-`l` S3 bound. -/
private theorem orderNumerator_s3_part_bound (d L N M j k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G : ManyBodyOpS (HypercubicTorus d L) N) {q₀ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * c₂ * momentFactor d L N Φ (2 * M - 3))) := by
  rw [orderNumerator_s3_part_eq d L N M j k G]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => orderNumerator_s3_lterm_bound d L N M j k l Φ
    hsing G hc₂ hGw hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by linarith [hc₂]) (momentFactor_nonneg d L N Φ _)))

/-- **Per-`(j,k)` term bound.**  The sandwiched commutator `(ô⁻)^k [T_j, ô⁻] (ô⁻)^{M-1-k}` (with
`T_j = (ô⁺)^j G (ô⁺)^{M-1-j}`) decomposes into the S1 middle `(−D)`, the S2 source and the S3
source; the triangle inequality plus the three part bounds give the total. -/
private theorem orderNumerator_jk_term_bound (d L N M j k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (G D : ManyBodyOpS (HypercubicTorus d L) N)
    (hnest : G * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * G = -D)
    {q₀ c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hD : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * D * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₁ * momentFactor d L N Φ (wl.length + wr.length))
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hj : j < M) (hk : k < M)
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * G
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j * G
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * c₁ * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * G
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j * G
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ j * (-D)
            * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
        + (staggeredOrderDensityOpS d L N false ^ k
            * (staggeredOrderDensityOpS d L N true ^ j * G
              * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
                  * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false
                  * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
          + staggeredOrderDensityOpS d L N false ^ k
            * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
              * G * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k))
      from by rw [orderNumerator_Tj_decomp d L N j (M - 1 - j) G D hnest]; noncomm_ring,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    Complex.add_re, Complex.add_re]
  refine (abs_add_le _ _).trans (add_le_add ?_ ((abs_add_le _ _).trans (add_le_add ?_ ?_)))
  · exact orderNumerator_s1_middle_bound d L N M j k Φ D hD hj hk hcond2 hbudget2
  · exact orderNumerator_s2_part_bound d L N M j k Φ hsing G hc₂ hGw hj hk hcond3 hbudget3
  · exact orderNumerator_s3_part_bound d L N M j k Φ hsing G hc₂ hGw hj hk hcond3 hbudget3

/-! ### The collected numerator bound -/

/-- **Generic order-density numerator bound.**  For a Hamiltonian `H` whose single order-density
commutator is `G = [H, ô⁺]` and whose nested commutator satisfies `[G, ô⁻] = −D`, the
★-variational numerator `⟨Φ, [(ô⁻)^M, [H, (ô⁺)^M]] Φ⟩` on a total-`Ŝ³` singlet `Φ` is bounded by
`M²` copies of the per-insertion bound built from the order-word expectation bounds of `D`
(constant `c₁`, word length `2M−2`) and of `G` (constant `c₂`, word length `2M−3`).

Instantiating `H` with the spin-`S` Heisenberg Hamiltonian gives the Anderson-tower numerator
estimate of Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer
2020), §4.2.2 Theorem 4.6 (eq. (4.2.64), p. 111); instantiating it with the Ising part `Ĥ_ZZ` gives
the residual numerator estimate of §5.3 Theorem 5.2 (eq. (5.3.4), p. 141). -/
theorem tower_numerator_bound_of_word_bounds (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (H G D : ManyBodyOpS (HypercubicTorus d L) N)
    (hG : H * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * H = G)
    (hnest : G * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * G = -D)
    {q₀ c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hD : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * D * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₁ * momentFactor d L N Φ (wl.length + wr.length))
    (hGw : ∀ wl wr : List Bool,
        3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
        ((wl.length + wr.length : ℕ) : ℝ)
            * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2 →
        |(star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re|
          ≤ 3 * c₂ * momentFactor d L N Φ (wl.length + wr.length))
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ M
        * (H * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * H)
      - (H * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * H)
        * staggeredOrderDensityOpS d L N false ^ M).mulVec Φ).re|
      ≤ (M : ℝ) * ((M : ℝ) * (3 * c₁ * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))))) := by
  rw [orderNumerator_eq_sum_j d L N M H G hG]
  refine (abs_re_dotProduct_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    ((M : ℝ) * (3 * c₁ * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))))) ?_)
    (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro j hj
  rw [orderMinusPow_commutator_eq]
  refine (abs_re_dotProduct_neg_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    (3 * c₁ * momentFactor d L N Φ (2 * M - 2)
      + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))
        + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * c₂ * momentFactor d L N Φ (2 * M - 3)))))
    ?_) (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro k hk
  exact orderNumerator_jk_term_bound d L N M j k Φ hsing G D hnest hc₂ hD hGw
    (Finset.mem_range.mp hj) (Finset.mem_range.mp hk) hcond2 hbudget2 hcond3 hbudget3

end LatticeSystem.Quantum
