import LatticeSystem.Quantum.SpinS.AndersonTowerPinch
import LatticeSystem.Quantum.SpinS.ManyBodyOperatorNorm

/-!
# Tasaki §4.2.2 Proposition 4.10: the pinch vector remainder bound (PR-6b-ii)

This module is the operator-norm / `L²`-vector analogue of the scalar pinch band identity
`cartWord_sphereAverage_pinch` (PR-3.3b).  It bounds the `L²` distance between the sphere average
`Op_{2j}Φ = (∫_{S²} (Ô_L^n)^{2j} dσ) Φ` and its rotationally invariant main part
`(4π/(2j+1)) (ô²)^j Φ`, *without* any singlet premise:

`√(vecNormSqRe (Op_{2j}Φ − (4π/(2j+1)) (ô²)^j Φ))`
`    ≤ cartPinchVecPoly j · (V·N)^{2j−1} · √(vecNormSqRe Φ)`.

The scalar band identity bounds `|⟨Φ, D_jΦ⟩.re|`; the `L²` vector norm `‖D_jΦ‖` involves `D_j†D_j`
and does **not** follow from it, so the remainder operator `D_j = Op_{2j} − (4π/(2j+1)) (ô²)^j` is
banded directly in operator norm.  The main parts cancel after grouping both the ordered
configurations `List.ofFn f` (moment-weighted, odd ones vanishing) and the squared configurations
`sqWord g` into their grouped normal form and matching per-configuration coefficients
(`sphereMoment_grouped_eq_orderSq_grouped`, mirroring the scalar `hMAIN`).  Each grouped
difference is banded by the singlet-free operator-norm swap chain
`cartWord_swapChain_manyBodyOperatorNormS_diff_le` at the clean `(V·N)^{2j−1}` scale (one commutator
factor `‖[ô^{(a)}, ô^{(b)}]‖ ≤ V·N` per swap).  The relative bound and the torus/LRO lower moment
`√R_{2j} ≥ q₀^j V^{2j} √R_0` are deferred to PR-6c.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.58)–(4.2.60), p. 108.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory LatticeSystem.Math
open scoped Matrix.Norms.Frobenius Nat

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Operator main-part cancellation -/

/-- **Operator main-part cancellation** (Prop 4.10 grouped normal form, operator-valued mirror of
the scalar `hMAIN`).  The moment-weighted grouped ordered configurations equal the rotationally
invariant grouped squared configurations up to `4π/(2j+1)`:
`∑_f moment(count f) • ô^{grouped(count f)} = (4π/(2j+1)) • ∑_g ô^{grouped(2·count g)}`.  Both
sides are grouped by count vector (`config_sum_eq_multinomial_sum_module`); the even count vectors
`k = 2h` match with coefficient `multinomial(2h)·moment(2h) = (4π/(2j+1))·multinomial(h)`
(`pinch_coeff_match`) and the odd ones vanish (`sphereMonomialMoment = 0`). -/
theorem sphereMoment_grouped_eq_orderSq_grouped (A : Λ → Bool) (j : ℕ) :
    (∑ f : Fin (2 * j) → Fin 3,
        ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
          • cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α)))
      = (4 * Real.pi / (2 * j + 1) : ℂ)
          • ∑ g : Fin j → Fin 3,
              cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α)) := by
  classical
  have hLM_op : (∑ f : Fin (2 * j) → Fin 3,
        ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
          • cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α)))
      = ∑ k ∈ Finset.Nat.antidiagonalTuple 3 (2 * j),
          Nat.multinomial Finset.univ k
            • (((sphereMonomialMoment k : ℝ) : ℂ) • cartWord A N (groupedFin3 k)) :=
    config_sum_eq_multinomial_sum_module (fun k =>
      ((sphereMonomialMoment k : ℝ) : ℂ) • cartWord A N (groupedFin3 k))
  have hRM_op : (∑ g : Fin j → Fin 3,
        cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α)))
      = ∑ h ∈ Finset.Nat.antidiagonalTuple 3 j,
          Nat.multinomial Finset.univ h • cartWord A N (groupedFin3 (fun α => 2 * h α)) :=
    config_sum_eq_multinomial_sum_module (fun k =>
      cartWord A N (groupedFin3 (fun α => 2 * k α)))
  have hDinj : Set.InjOn (fun h : Fin 3 → ℕ => fun α => 2 * h α)
      (Finset.Nat.antidiagonalTuple 3 j : Finset (Fin 3 → ℕ)) := by
    intro h₁ _ h₂ _ he
    funext α
    have hα : 2 * h₁ α = 2 * h₂ α := congrFun he α
    omega
  have hsub : (Finset.Nat.antidiagonalTuple 3 j).image
        (fun h : Fin 3 → ℕ => fun α => 2 * h α)
      ⊆ Finset.Nat.antidiagonalTuple 3 (2 * j) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨h, hh, rfl⟩ := hk
    rw [Finset.Nat.mem_antidiagonalTuple] at hh ⊢
    simp only [← Finset.mul_sum, hh]
  have hvanish : ∀ k ∈ Finset.Nat.antidiagonalTuple 3 (2 * j),
      k ∉ (Finset.Nat.antidiagonalTuple 3 j).image
            (fun h : Fin 3 → ℕ => fun α => 2 * h α) →
      Nat.multinomial Finset.univ k
          • (((sphereMonomialMoment k : ℝ) : ℂ) • cartWord A N (groupedFin3 k)) = 0 := by
    intro k hk hkni
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    have hodd : ¬ (∀ i, Even (k i)) := by
      intro heven
      apply hkni
      rw [Finset.mem_image]
      refine ⟨fun α => k α / 2, ?_, ?_⟩
      · have h2 : 2 * (∑ α : Fin 3, k α / 2) = 2 * j := by
          rw [Finset.mul_sum,
            Finset.sum_congr rfl fun α _ =>
              (by obtain ⟨c, hc⟩ := heven α; omega : 2 * (k α / 2) = k α)]
          exact hk
        rw [Finset.Nat.mem_antidiagonalTuple]
        show ∑ i, k i / 2 = j
        omega
      · funext α
        change 2 * (k α / 2) = k α
        obtain ⟨c, hc⟩ := heven α
        omega
    simp only [sphereMonomialMoment, if_neg hodd, Complex.ofReal_zero, zero_smul, smul_zero]
  rw [hLM_op, hRM_op, Finset.smul_sum, ← Finset.sum_subset hsub hvanish, Finset.sum_image hDinj]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [Finset.Nat.mem_antidiagonalTuple] at hh
  have hscalC : (Nat.multinomial Finset.univ (fun α => 2 * h α) : ℂ)
        * ((sphereMonomialMoment (fun α => 2 * h α) : ℝ) : ℂ)
      = (4 * Real.pi / (2 * j + 1) : ℂ) * (Nat.multinomial Finset.univ h : ℂ) := by
    have hreal : (Nat.multinomial Finset.univ (fun α => 2 * h α) : ℝ)
          * sphereMonomialMoment (fun α => 2 * h α)
        = 4 * Real.pi / (2 * j + 1) * (Nat.multinomial Finset.univ h : ℝ) := by
      have hmom : sphereMonomialMoment (fun α => 2 * h α)
          = 4 * Real.pi * ((∏ i, ((2 * h i - 1)‼ : ℕ)) : ℝ) / (((2 * (∑ i, h i)) + 1)‼ : ℝ) := by
        have hev : ∀ i, Even (2 * h i) := fun i => ⟨h i, two_mul (h i)⟩
        rw [sphereMonomialMoment, if_pos hev, Finset.mul_sum Finset.univ h 2]
        push_cast; ring
      rw [hmom, LatticeSystem.Math.pinch_coeff_match h, hh]
    calc (Nat.multinomial Finset.univ (fun α => 2 * h α) : ℂ)
          * ((sphereMonomialMoment (fun α => 2 * h α) : ℝ) : ℂ)
        = (((Nat.multinomial Finset.univ (fun α => 2 * h α) : ℝ)
            * sphereMonomialMoment (fun α => 2 * h α) : ℝ) : ℂ) := by push_cast; ring
      _ = ((4 * Real.pi / (2 * j + 1) * (Nat.multinomial Finset.univ h : ℝ) : ℝ) : ℂ) := by
          rw [hreal]
      _ = (4 * Real.pi / (2 * j + 1) : ℂ) * (Nat.multinomial Finset.univ h : ℂ) := by
          push_cast; ring
  rw [← Nat.cast_smul_eq_nsmul ℂ (Nat.multinomial Finset.univ (fun α => 2 * h α)),
    ← Nat.cast_smul_eq_nsmul ℂ (Nat.multinomial Finset.univ h), smul_smul, smul_smul, hscalC]

/-! ### The vector pinch polynomial prefactor -/

/-- **Vector pinch polynomial prefactor** `cartPinchVecPoly j`: the operator-norm analogue of
`cartPinchPoly`.  It drops the scalar re-band's extra `9·(2j)` factor (the clean operator swap band
`cartWord_swapChain_manyBodyOperatorNormS_diff_le` yields `k·(V·N)^{n−1}` with no such factor),
retaining the total sphere-moment weight, the `(4π/(2j+1))·3^j` squared-configuration weight and the
branching bound `(2j)·(2j)`. -/
noncomputable def cartPinchVecPoly (j : ℕ) : ℝ :=
  ((∑ f : Fin (2 * j) → Fin 3, sphereMonomialMoment (fun α => (List.ofFn f).count α))
      + 4 * Real.pi / (2 * j + 1) * 3 ^ j)
    * ((2 * j) * (2 * j))

/-! ### The operator-norm pinch band -/

/-- **Operator-norm pinch band** (Prop 4.10, operator-valued core).  `‖D_j‖ ≤ cartPinchVecPoly j
· (V·N)^{2j−1}` where `D_j = ∫_{S²}(Ô_L^n)^{2j}dσ − (4π/(2j+1))(ô²)^j`.  The sphere average and
`(ô²)^j` expand into moment-weighted ordered and squared Cartesian words; the main parts cancel
(`sphereMoment_grouped_eq_orderSq_grouped`), and each grouped difference is banded at
`(2j)²·(V·N)^{2j−1}` by the singlet-free operator swap chain.  No singlet premise. -/
theorem sphereAverage_orderSq_manyBodyOperatorNormS_diff_le (A : Λ → Bool) (hN : 1 ≤ N) (j : ℕ) :
    manyBodyOperatorNormS
        ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j) ∂volume.toSphere)
          - (4 * Real.pi / (2 * j + 1) : ℂ) • (orderSqOp A N ^ j))
      ≤ cartPinchVecPoly j * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1) := by
  classical
  -- Sphere average as a moment-weighted sum of ordered Cartesian words.
  have hopA : (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j) ∂volume.toSphere)
      = ∑ f : Fin (2 * j) → Fin 3,
          ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
            • cartWord A N (List.ofFn f) := by
    rw [sphereAverage_directionStaggeredOp_pow A N (2 * j)]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [cartWord_ofFn, funext (fun α => LatticeSystem.Math.count_ofFn_eq_card_filter f α)]
  have hBj : orderSqOp A N ^ j = ∑ g : Fin j → Fin 3, cartWord A N (sqWord g) :=
    orderSqOp_pow_eq_sum_cartWord A N j
  -- Difference decomposition with cancelled main part.
  have hdecomp : (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j) ∂volume.toSphere)
          - (4 * Real.pi / (2 * j + 1) : ℂ) • (orderSqOp A N ^ j)
      = (∑ f : Fin (2 * j) → Fin 3,
            ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
              • (cartWord A N (List.ofFn f)
                  - cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α))))
        - (4 * Real.pi / (2 * j + 1) : ℂ)
            • (∑ g : Fin j → Fin 3, (cartWord A N (sqWord g)
                - cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α)))) := by
    have hmain := sphereMoment_grouped_eq_orderSq_grouped (Λ := Λ) (N := N) A j
    rw [hopA, hBj,
      show (∑ f : Fin (2 * j) → Fin 3,
            ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
              • (cartWord A N (List.ofFn f)
                  - cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α))))
          = (∑ f : Fin (2 * j) → Fin 3,
              ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
                • cartWord A N (List.ofFn f))
            - (∑ f : Fin (2 * j) → Fin 3,
              ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
                • cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α))) from by
        simp only [smul_sub, Finset.sum_sub_distrib],
      show (4 * Real.pi / (2 * j + 1) : ℂ)
            • (∑ g : Fin j → Fin 3, (cartWord A N (sqWord g)
                - cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α))))
          = (4 * Real.pi / (2 * j + 1) : ℂ) • (∑ g : Fin j → Fin 3, cartWord A N (sqWord g))
            - (4 * Real.pi / (2 * j + 1) : ℂ)
                • (∑ g : Fin j → Fin 3,
                    cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α))) from by
        rw [Finset.sum_sub_distrib, smul_sub]]
    rw [hmain]
    abel
  -- Per-configuration operator swap bands at the (V·N)^{2j−1} scale.
  have hRL : ∀ f : Fin (2 * j) → Fin 3, manyBodyOperatorNormS
      (cartWord A N (List.ofFn f)
        - cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α)))
      ≤ ((2 * j) * (2 * j) : ℝ) * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1) := by
    intro f
    obtain ⟨k, hk, hchain⟩ := ofFn_swapChain_groupedFin3 f
    have hlen : (List.ofFn f).length = 2 * j := List.length_ofFn
    refine le_trans (cartWord_swapChain_manyBodyOperatorNormS_diff_le A N hN (2 * j) hchain hlen) ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  have hRR : ∀ g : Fin j → Fin 3, manyBodyOperatorNormS
      (cartWord A N (sqWord g)
        - cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α)))
      ≤ ((2 * j) * (2 * j) : ℝ) * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1) := by
    intro g
    obtain ⟨k, hk, hchain⟩ := ofFn_swapChain_groupedFin3 ((sqWord g).get)
    rw [List.ofFn_get] at hchain
    have hcnt : (fun i => (sqWord g).count i) = (fun α => 2 * (List.ofFn g).count α) :=
      funext (fun i => count_sqWord g i)
    rw [hcnt] at hchain
    have hlen : (sqWord g).length = 2 * j := length_sqWord g
    refine le_trans (cartWord_swapChain_manyBodyOperatorNormS_diff_le A N hN (2 * j) hchain hlen) ?_
    rw [hlen] at hk
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  -- Aggregate the two grouped differences via the triangle, scalar and sum inequalities.
  have hcnorm : ‖(4 * Real.pi / (2 * j + 1) : ℂ)‖ = 4 * Real.pi / (2 * j + 1) := by
    rw [show (4 * Real.pi / (2 * j + 1) : ℂ) = ((4 * Real.pi / (2 * j + 1) : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hL : manyBodyOperatorNormS (∑ f : Fin (2 * j) → Fin 3,
        ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
          • (cartWord A N (List.ofFn f)
              - cartWord A N (groupedFin3 (fun α => (List.ofFn f).count α))))
      ≤ (∑ f : Fin (2 * j) → Fin 3, sphereMonomialMoment (fun α => (List.ofFn f).count α))
          * (((2 * j) * (2 * j)) * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1)) := by
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun f _ => ?_)
    rw [manyBodyOperatorNormS_smul, Complex.norm_real,
      Real.norm_of_nonneg (sphereMonomialMoment_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hRL f) (sphereMonomialMoment_nonneg _)
  have hR : manyBodyOperatorNormS ((4 * Real.pi / (2 * j + 1) : ℂ)
        • (∑ g : Fin j → Fin 3, (cartWord A N (sqWord g)
            - cartWord A N (groupedFin3 (fun α => 2 * (List.ofFn g).count α)))))
      ≤ 4 * Real.pi / (2 * j + 1)
          * ((3 : ℝ) ^ j * ((2 * j) * (2 * j)) * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1)) := by
    rw [manyBodyOperatorNormS_smul, hcnorm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun g _ => hRR g)) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  rw [hdecomp]
  refine le_trans (manyBodyOperatorNormS_sub_le _ _) (le_trans (add_le_add hL hR) (le_of_eq ?_))
  rw [cartPinchVecPoly]; ring

/-! ### The vector pinch bridge -/

/-- **PR-6b vector pinch bridge** (Tasaki §4.2.2 (4.2.58)/(4.2.59) の `L²` ベクトル版).  Applying
`D_j` to `Φ`, the `L²` distance between the sphere average `Op_{2j}Φ` and its rotationally invariant
main part `(4π/(2j+1))(ô²)^jΦ` is bounded by `cartPinchVecPoly j · (V·N)^{2j−1} · ‖Φ‖`.  Applies the
operator-norm band `sphereAverage_orderSq_manyBodyOperatorNormS_diff_le` through the operator-norm
vector bound `sqrt_vecNormSqRe_mulVec_le`.  Singlet-free, raw `Λ`, torus/LRO-independent
(relativisation is PR-6c). -/
theorem sphereAverage_orderSq_vecRemainder_le (A : Λ → Bool) (hN : 1 ≤ N)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (j : ℕ) :
    Real.sqrt (vecNormSqRe
        ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j)
              ∂volume.toSphere).mulVec Φ
          - (4 * Real.pi / (2 * j + 1) : ℂ) • ((orderSqOp A N ^ j).mulVec Φ)))
      ≤ cartPinchVecPoly j * ((Fintype.card Λ : ℝ) * N) ^ (2 * j - 1)
          * Real.sqrt (vecNormSqRe Φ) := by
  rw [show (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j)
            ∂volume.toSphere).mulVec Φ
        - (4 * Real.pi / (2 * j + 1) : ℂ) • ((orderSqOp A N ^ j).mulVec Φ)
      = ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * j) ∂volume.toSphere)
          - (4 * Real.pi / (2 * j + 1) : ℂ) • (orderSqOp A N ^ j)).mulVec Φ from by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec]]
  refine le_trans (sqrt_vecNormSqRe_mulVec_le _ Φ) ?_
  exact mul_le_mul_of_nonneg_right
    (sphereAverage_orderSq_manyBodyOperatorNormS_diff_le A hN j) (Real.sqrt_nonneg _)

end LatticeSystem.Quantum
