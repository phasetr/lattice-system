import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSU2

/-!
# Tasaki §4.2.1 Theorem 4.6: order-word sectors and swap-telescoping estimates

The sector structure of the order-density words entering the R1 induction: the total-spin sector
commutators `[Ŝ³_tot, Ô^±] = ±Ô^±` and the eigenvalue action on words (P8-1, P8-2), the generic
combinatorial pieces used in the R1 induction (`mCharge`, word products, norm bounds) (P8-3), and
the expectation telescoping of adjacent swaps of order densities (P8-4).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Sector commutators `[Ŝ³_tot, Ô^±] = ±Ô^±` (P8-1) -/

/-- Per-site step of `[Ŝ³_tot, Ô⁺] = Ô⁺`: on-site Cartan relation `[Ŝ³, Ŝ⁺] = Ŝ⁺`. -/
private theorem spinSSiteOp3_commutator_staggeredRaisingOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredRaisingOpS A N - staggeredRaisingOpS A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus x N := by
  unfold staggeredRaisingOpS spinSSiteOp3 spinSSiteOpPlus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOpPlus]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOpPlus N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Sector commutator** `[Ŝ³_tot, Ô_L⁺] = Ô_L⁺` (the raising order operator increases the total
magnetization by one). -/
theorem totalSpinSOp3_commutator_staggeredRaisingOpS (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredRaisingOpS A N - staggeredRaisingOpS A N * totalSpinSOp3 Λ N
      = staggeredRaisingOpS A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [staggeredRaisingOpS]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredRaisingOpS]

/-- Per-site step of `[Ŝ³_tot, Ô⁻] = −Ô⁻`: on-site Cartan relation `[Ŝ³, Ŝ⁻] = −Ŝ⁻`. -/
private theorem spinSSiteOp3_commutator_staggeredLoweringOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSSiteOp3 x N
      = -((if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus x N) := by
  unfold staggeredLoweringOpS spinSSiteOp3 spinSSiteOpMinus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOpMinus, onSiteS_neg,
      smul_neg]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOpMinus N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Sector commutator** `[Ŝ³_tot, Ô_L⁻] = −Ô_L⁻` (the lowering order operator decreases the total
magnetization by one). -/
theorem totalSpinSOp3_commutator_staggeredLoweringOpS (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * totalSpinSOp3 Λ N
      = -staggeredLoweringOpS A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [staggeredLoweringOpS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredLoweringOpS]

/-! ### Word sector eigenvalue (P8-2) -/

/-- **Per-volume sector commutator** `[Ŝ³_tot, ô^b] = ε_b ô^b` (`ε_true = +1`, `ε_false = −1`):
the per-volume raising/lowering density shifts the total magnetization by `±1`. -/
theorem totalSpinSOp3_commutator_orderDensity (d L N : ℕ) [NeZero L] (b : Bool) :
    totalSpinSOp3 (HypercubicTorus d L) N * staggeredOrderDensityOpS d L N b
        - staggeredOrderDensityOpS d L N b * totalSpinSOp3 (HypercubicTorus d L) N
      = (if b then (1 : ℂ) else (-1 : ℂ)) • staggeredOrderDensityOpS d L N b := by
  cases b
  · rw [show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, totalSpinSOp3_commutator_staggeredLoweringOpS]
    simp [smul_neg]
  · rw [show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, totalSpinSOp3_commutator_staggeredRaisingOpS]
    simp

/-- **Single-step magnetization shift**: if `Ŝ³_tot v = λ v` then `Ŝ³_tot (ô^b v) = (λ+ε_b)(ô^b v)`
(`ε_true = +1`, `ε_false = −1`). -/
theorem totalSpinSOp3_mulVec_orderDensity_eigenvec (d L N : ℕ) [NeZero L] (b : Bool)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = lam • v) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((staggeredOrderDensityOpS d L N b).mulVec v)
      = (lam + (if b then (1 : ℂ) else (-1 : ℂ)))
          • (staggeredOrderDensityOpS d L N b).mulVec v := by
  have hcomm := totalSpinSOp3_commutator_orderDensity d L N b
  have key : totalSpinSOp3 (HypercubicTorus d L) N * staggeredOrderDensityOpS d L N b
      = staggeredOrderDensityOpS d L N b * totalSpinSOp3 (HypercubicTorus d L) N
        + (if b then (1 : ℂ) else (-1 : ℂ)) • staggeredOrderDensityOpS d L N b := by
    rw [← hcomm]; abel
  rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul]

/-- The **net magnetization charge** `m(w) = #{true} − #{false}` of an order word `w` (each `ô⁺`
contributes `+1`, each `ô⁻` contributes `−1`), as the sum of per-letter signs. -/
def mCharge (w : List Bool) : ℂ := (w.map (fun b => if b then (1 : ℂ) else (-1 : ℂ))).sum

@[simp] theorem mCharge_nil : mCharge [] = 0 := by simp [mCharge]

theorem mCharge_cons (b : Bool) (w : List Bool) :
    mCharge (b :: w) = (if b then (1 : ℂ) else (-1 : ℂ)) + mCharge w := by
  rw [mCharge, List.map_cons, List.sum_cons, mCharge]

/-- The net charge is real-valued: `(m(w)).im = 0`. -/
@[simp] theorem mCharge_im (w : List Bool) : (mCharge w).im = 0 := by
  induction w with
  | nil => simp
  | cons b w ih => rw [mCharge_cons, Complex.add_im, ih, add_zero]; split_ifs <;> simp

/-- Cons recursion for the ordered word product: `ô^{b::w} = ô^b · ô^{w}`. -/
theorem orderWordProd_cons (d L N : ℕ) [NeZero L] (b : Bool) (w : List Bool) :
    orderWordProd d L N (b :: w)
      = staggeredOrderDensityOpS d L N b * orderWordProd d L N w := by
  rw [orderWordProd, orderWordProd, List.map_cons, List.prod_cons]

/-- Append recursion for the ordered word product: `ô^{w ++ w'} = ô^{w} · ô^{w'}`. -/
theorem orderWordProd_append (d L N : ℕ) [NeZero L] (w w' : List Bool) :
    orderWordProd d L N (w ++ w')
      = orderWordProd d L N w * orderWordProd d L N w' := by
  rw [orderWordProd, orderWordProd, orderWordProd, List.map_append, List.prod_append]

/-- **Word sector eigenvalue**: for a total-`Ŝ³` singlet `v` (`Ŝ³_tot v = 0`), the ordered word
product is an eigenvector `Ŝ³_tot (ô^{w} v) = m(w) (ô^{w} v)` with eigenvalue the net charge. -/
theorem totalSpinSOp3_mulVec_orderWordProd_eigenvec (d L N : ℕ) [NeZero L] (w : List Bool)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = 0) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec ((orderWordProd d L N w).mulVec v)
      = mCharge w • (orderWordProd d L N w).mulVec v := by
  induction w with
  | nil =>
    rw [orderWordProd, List.map_nil, List.prod_nil, Matrix.one_mulVec, mCharge_nil, zero_smul, hv]
  | cons b w ih =>
    rw [orderWordProd_cons, ← Matrix.mulVec_mulVec,
      totalSpinSOp3_mulVec_orderDensity_eigenvec d L N b ih]
    congr 1
    rw [mCharge_cons]; ring

/-! ### Generic pieces for the R1 induction (P8-3) -/

/-- The `p̂`-moments are strictly positive under the LRO entry: `0 < mₙ`. -/
theorem phatMoment_pos_of_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq0 : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (n : ℕ) :
    0 < phatMoment d L N Φ n := by
  cases n with
  | zero => exact hm0
  | succ k =>
    have h := phatMoment_ge_of_lro d L N Φ hq0.le hm0 hlro k
    have hpos : 0 < (2 * q₀) ^ (k + 1) * phatMoment d L N Φ 0 :=
      mul_pos (pow_pos (mul_pos (by norm_num) hq0) (k + 1)) hm0
    exact lt_of_lt_of_le hpos h

/-- **Per-volume commutator as a scalar multiple of total spin** `[ô⁺, ô⁻] = (2/V²) Ŝ³_tot`. -/
theorem staggeredOrderDensity_commutator_eq (d L N : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
      = (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹)
          • ((2 : ℂ) • totalSpinSOp3 (HypercubicTorus d L) N) := by
  rw [show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl,
    show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, staggeredOrder_commutator]

/-- The net charge has modulus at most the word length: `‖m(w)‖ ≤ |w|` (sum of `±1`s). -/
theorem mCharge_norm_le (w : List Bool) : ‖mCharge w‖ ≤ (w.length : ℝ) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [mCharge_cons, List.length_cons]
    calc ‖(if b then (1 : ℂ) else (-1 : ℂ)) + mCharge w‖
        ≤ ‖(if b then (1 : ℂ) else (-1 : ℂ))‖ + ‖mCharge w‖ := norm_add_le _ _
      _ ≤ 1 + (w.length : ℝ) := by
          gcongr
          · split_ifs <;> simp
      _ = ((w.length + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Single-swap factorization** of the order-word product difference:
`ô^{pre++a::b::suf} − ô^{pre++b::a::suf} = ô^{pre} [ô^a, ô^b] ô^{suf}`. -/
theorem orderWordProd_swap_diff_eq (d L N : ℕ) [NeZero L] (pre suf : List Bool) (a b : Bool) :
    orderWordProd d L N (pre ++ a :: b :: suf) - orderWordProd d L N (pre ++ b :: a :: suf)
      = orderWordProd d L N pre
        * (staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
            - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a)
        * orderWordProd d L N suf := by
  have hexp : ∀ x y : Bool, orderWordProd d L N (pre ++ x :: y :: suf)
      = orderWordProd d L N pre
        * (staggeredOrderDensityOpS d L N x * staggeredOrderDensityOpS d L N y)
        * orderWordProd d L N suf := by
    intro x y
    simp only [orderWordProd, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    noncomm_ring
  rw [hexp, hexp, ← sub_mul, ← mul_sub]

/-- **Convex-combination deviation**: if `c · |s| = 1` and every term `f i` lies within `D` of `x`,
then `x` lies within `D` of the uniform average `c · ∑ f`. -/
theorem abs_sub_smul_sum_le {ι : Type*} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (x : ℝ) (f : ι → ℝ) (D : ℝ) (hcard : c * (s.card : ℝ) = 1)
    (hbound : ∀ i ∈ s, |x - f i| ≤ D) :
    |x - c * ∑ i ∈ s, f i| ≤ D := by
  have hx : x = c * ∑ _i ∈ s, x := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]
  have hstep : x - c * ∑ i ∈ s, f i = c * ∑ i ∈ s, (x - f i) := by
    rw [Finset.sum_sub_distrib, mul_sub, ← hx]
  rw [hstep, abs_mul, abs_of_nonneg hc]
  calc c * |∑ i ∈ s, (x - f i)|
      ≤ c * ∑ i ∈ s, |x - f i| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ c * ∑ _i ∈ s, D := by gcongr with i hi; exact hbound i hi
    _ = D := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]

/-- **Eigenvalue modulus is bounded by the operator norm**: if `B v = λ v` for `v ≠ 0`, then
`‖λ‖ ≤ ‖B‖`.  This is the uniform `|λ_suf| ≤ N/V` engine for the renormalized R1 estimate. -/
theorem eigenvalue_norm_le_manyBodyOperatorNormS {B : ManyBodyOpS Λ N} {lam : ℂ}
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ≠ 0) (h : B.mulVec v = lam • v) :
    ‖lam‖ ≤ manyBodyOperatorNormS B := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM]
  set x : EuclideanSpace ℂ (Λ → Fin (N + 1)) := WithLp.toLp 2 v with hxdef
  have hxne : x ≠ 0 := by
    intro hc
    apply hv
    have := congrArg WithLp.ofLp hc
    simpa [hxdef] using this
  have happ : Matrix.toEuclideanCLM (𝕜 := ℂ) B x = lam • x := by
    rw [hxdef, Matrix.toEuclideanCLM_toLp, h, WithLp.toLp_smul]
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) B).le_opNorm x
  rw [happ, norm_smul] at h1
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hxne)

/-! ### Expectation telescoping of swaps (P8-4) -/

/-- The order-density commutator for any pair `a, b` is a scalar multiple of `Ŝ³_tot`:
`ô^a ô^b − ô^b ô^a = σ(a,b) (2/V²) Ŝ³_tot`, `σ = 0` if `a = b`, `±1` otherwise. -/
theorem orderDensity_comm_ab (d L N : ℕ) [NeZero L] (a b : Bool) :
    staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
        - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a
      = (if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
          • ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹)
              • ((2 : ℂ) • totalSpinSOp3 (HypercubicTorus d L) N)) := by
  rcases a with _ | _ <;> rcases b with _ | _
  · simp
  · rw [← staggeredOrderDensity_commutator_eq]; norm_num
  · rw [show staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
        = -(staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false) from by
        rw [neg_sub], ← staggeredOrderDensity_commutator_eq]
    norm_num
  · simp

/-- **Single-swap expectation difference**: for a singlet `Φ`, the expectation of an order word
changes under one adjacent transposition by a real scalar (`σ(a,b) · 2 m(suf)/V²`) times the
expectation of the shortened (charge-removed) word. -/
theorem orderWordProd_swap_dotProduct_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (pre suf : List Bool) (a b : Bool) :
    (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ a :: b :: suf)).mulVec Φ)
        - (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ)
      = ((if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
            * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)))
          * (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ) := by
  have heig : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec ((orderWordProd d L N suf).mulVec Φ)
      = mCharge suf • (orderWordProd d L N suf).mulVec Φ :=
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N suf hsing
  have hvec : (orderWordProd d L N (pre ++ a :: b :: suf)
        - orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ
      = ((if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
            * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)))
          • (orderWordProd d L N (pre ++ suf)).mulVec Φ := by
    rw [orderWordProd_swap_diff_eq, orderDensity_comm_ab, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, heig,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, ← orderWordProd_append, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, hvec, dotProduct_smul, smul_eq_mul]

/-- The order-density commutator acts on a word vector as the scalar `(2/V²) m(suf)`. -/
theorem orderCommutator_mulVec_orderWordProd (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (suf : List Bool) :
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true).mulVec
        ((orderWordProd d L N suf).mulVec Φ)
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))
          • (orderWordProd d L N suf).mulVec Φ := by
  rw [staggeredOrderDensity_commutator_eq, Matrix.smul_mulVec, Matrix.smul_mulVec,
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N suf hsing, smul_smul, smul_smul]
  congr 1
  ring

/-- **Single-swap real-expectation bound**: one adjacent transposition changes the real part of the
order-word expectation by at most `(N/V)` times the shortened word's real expectation. -/
theorem orderWordProd_swap_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (pre suf : List Bool) (a b : Bool) :
    |(star Φ ⬝ᵥ (orderWordProd d L N (pre ++ a :: b :: suf)).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ).re|
      ≤ (N : ℝ) / (L : ℝ) ^ d
          * |(star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ).re| := by
  rw [← Complex.sub_re, orderWordProd_swap_dotProduct_eq d L N Φ hsing pre suf a b]
  set κ := (if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
      * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)) with hκ
  have hLim : ((((L : ℂ) ^ d)⁻¹).im) = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) from by push_cast; ring]
    exact Complex.ofReal_im _
  have hκim : κ.im = 0 := by
    rw [hκ]
    simp only [Complex.mul_im, Complex.mul_re, mCharge_im, hLim]
    split_ifs <;> simp
  rw [Complex.mul_re, hκim, zero_mul, sub_zero, abs_mul]
  by_cases hu : (orderWordProd d L N suf).mulVec Φ = 0
  · have hz0 : star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ = 0 := by
      rw [orderWordProd_append, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero, dotProduct_zero]
    rw [hz0]; simp
  · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hknorm : ‖((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))‖
        ≤ (N : ℝ) / (L : ℝ) ^ d :=
      le_trans (eigenvalue_norm_le_manyBodyOperatorNormS hu
          (orderCommutator_mulVec_orderWordProd d L N Φ hsing suf))
        (staggeredOrderDensity_commutator_manyBodyOperatorNormS_le d L N hN)
    have hσ : ‖(if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))‖ ≤ 1 := by
      split_ifs <;> simp
    have hκeq : κ = (κ.re : ℂ) := Complex.ext rfl (by rw [hκim, Complex.ofReal_im])
    calc |κ.re| = ‖(κ.re : ℂ)‖ := (Complex.norm_real _).symm
      _ = ‖κ‖ := by rw [← hκeq]
      _ = ‖(if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))‖
            * ‖((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))‖ := by
          rw [hκ, norm_mul]
      _ ≤ 1 * ((N : ℝ) / (L : ℝ) ^ d) := by
          apply mul_le_mul hσ hknorm (norm_nonneg _) (by norm_num)
      _ = (N : ℝ) / (L : ℝ) ^ d := one_mul _

end LatticeSystem.Quantum
