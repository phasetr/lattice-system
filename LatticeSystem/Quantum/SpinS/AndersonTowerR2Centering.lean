/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 3 — Lemma R2 in Tasaki's centering form.

The geometric-mean bound `renormalized_inserted_product_bound` (AndersonTowerLocality) is true but too
weak for the numerator (4.2.64): its terms are totally charge-balanced but split-unbalanced, so the
geometric mean of split-length moments blows up exponentially.  Tasaki's Lemma R2 (eq. (4.2.68)) is
the split-INDEPENDENT bound `≤ 3 g₀ ⟨p̂^{K/2}⟩` obtained by an induction on `K` that centers the
inserted operator (Step A) and then applies Cauchy–Schwarz + R1 at the center (Step B).

To avoid formalizing the full support-based locality class, we encode locality as the
**norm-decay of iterated order-density commutators**: `IsR2LocalUpTo` requires
`‖[ô^{u_k},…,[ô^{u_1},G]…]‖ ≤ (2ζo₀/V)^{|u|} g₀` for all words `u` of length `≤ K`.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-! ### Iterated order-density commutators and the local-decay class (R2 commit 1) -/

/-- The integer sign of an order letter: `+1` for `true` (raising), `−1` for `false` (lowering). -/
def orderSignZ (b : Bool) : ℤ := if b then 1 else -1

/-- The net integer charge of an order word. -/
def wordChargeZ (w : List Bool) : ℤ := (w.map orderSignZ).sum

@[simp] theorem wordChargeZ_nil : wordChargeZ ([] : List Bool) = 0 := by simp [wordChargeZ]

theorem wordChargeZ_cons (b : Bool) (w : List Bool) :
    wordChargeZ (b :: w) = orderSignZ b + wordChargeZ w := by
  simp [wordChargeZ]

/-- One order-density commutator `[ô^b, G] = ô^b G − G ô^b`. -/
noncomputable def orderComm [NeZero L] (b : Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) : ManyBodyOpS (HypercubicTorus d L) N :=
  staggeredOrderDensityOpS d L N b * G - G * staggeredOrderDensityOpS d L N b

/-- The iterated order-density commutator `[ô^{u_k}, [ …, [ô^{u_1}, G] … ]]` along a word `u`
(applied left-to-right). -/
noncomputable def iterOrderComm [NeZero L] :
    List Bool → ManyBodyOpS (HypercubicTorus d L) N → ManyBodyOpS (HypercubicTorus d L) N
  | [], G => G
  | b :: bs, G => iterOrderComm bs (orderComm b G)

@[simp] theorem iterOrderComm_nil [NeZero L] (G : ManyBodyOpS (HypercubicTorus d L) N) :
    iterOrderComm [] G = G := rfl

theorem iterOrderComm_cons [NeZero L] (b : Bool) (bs : List Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    iterOrderComm (b :: bs) G = iterOrderComm bs (orderComm b G) := rfl

/-- **Local-decay class up to depth `K`**: `G` is in the class with constants `ζ, o₀, g₀` if every
iterated order-density commutator of `G` along a word of length `≤ K` has norm at most
`(2ζo₀/V)^{|u|} g₀`.  This encodes Tasaki's per-bond locality (each `[ô^·, ·]` decays by `2ζo₀/V`)
without an explicit support predicate. -/
structure IsR2LocalUpTo [NeZero L] (K : ℕ) (ζ o₀ g₀ : ℝ)
    (G : ManyBodyOpS (HypercubicTorus d L) N) : Prop where
  g0_nonneg : 0 ≤ g₀
  norm_iter : ∀ u : List Bool, u.length ≤ K →
    manyBodyOperatorNormS (iterOrderComm u G)
      ≤ ((2 * ζ * o₀) / (L : ℝ) ^ d) ^ u.length * g₀

/-- `G` itself (depth-0 commutator) has norm `≤ g₀` in the local-decay class. -/
theorem IsR2LocalUpTo.norm_le [NeZero L] {K : ℕ} {ζ o₀ g₀ : ℝ}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (h : IsR2LocalUpTo K ζ o₀ g₀ G) :
    manyBodyOperatorNormS G ≤ g₀ := by
  have := h.norm_iter [] (Nat.zero_le _)
  simpa using this

/-! ### Step A: the centering telescope of an inserted operator (R2 commit 2) -/

/-- Operator-level cons identity for the word product. -/
theorem orderWordProd_mul_cons [NeZero L] (b : Bool) (w : List Bool) :
    orderWordProd d L N (b :: w)
      = staggeredOrderDensityOpS d L N b * orderWordProd d L N w := by
  simp [orderWordProd, List.map_cons, List.prod_cons]

/-- The `i`-th telescope term of `[orderWordProd w, G]`: the prefix product, the single-letter
order-density commutator at position `i`, then the suffix product. -/
noncomputable def telescopeTerm [NeZero L] (w : List Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) (i : ℕ) : ManyBodyOpS (HypercubicTorus d L) N :=
  orderWordProd d L N (w.take i) * orderComm (w.getD i false) G
    * orderWordProd d L N (w.drop (i + 1))

/-- **Step A telescope (eq. (4.2.68) centering).**  The commutator of a word product with `G`
expands as the sum over positions `i` of the prefix–`[ô^{w_i},G]`–suffix terms.  Moving `G` from
one end to the center is the difference of two such partial telescopes; each term carries one fewer
order factor and the decayed commutator `orderComm`. -/
theorem orderWordProd_comm_eq_telescope [NeZero L] (w : List Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    orderWordProd d L N w * G - G * orderWordProd d L N w
      = ∑ i ∈ Finset.range w.length, telescopeTerm w G i := by
  induction w with
  | nil =>
    simp [orderWordProd, telescopeTerm]
  | cons b w ih =>
    rw [List.length_cons, Finset.sum_range_succ', orderWordProd_mul_cons]
    have hshift : ∀ i ∈ Finset.range w.length,
        telescopeTerm (b :: w) G (i + 1)
          = staggeredOrderDensityOpS d L N b * telescopeTerm w G i := by
      intro i _
      unfold telescopeTerm
      rw [List.take_succ_cons, List.getD_cons_succ, List.drop_succ_cons, orderWordProd_mul_cons]
      noncomm_ring
    rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum, ← ih]
    have h0 : telescopeTerm (b :: w) G 0
        = orderComm b G * orderWordProd d L N w := by
      simp only [telescopeTerm, List.take_zero, List.getD_cons_zero, List.drop_succ_cons,
        List.drop_zero, orderWordProd, List.map_nil, List.prod_nil, one_mul]
    rw [h0, orderComm]
    noncomm_ring

/-! ### Step B: the symmetric-split central bound (R2 commit 3) -/

/-- **Step B (central Cauchy–Schwarz, symmetric split).**  When the inserted operator sits exactly
at the center of a length-`2n` order word (equal left/right words `w`), the geometric mean of the
two half-radicands collapses to a single moment: `|Re⟨Φ, ô^w G ô^w Φ⟩| ≤ (3/2)‖G‖ P_{|w|}`.  This
is the target shape of the Anderson-tower numerator; the centering telescope (Step A) reduces an
arbitrarily placed `G` to this symmetric form plus decayed error terms. -/
theorem renormalized_inserted_product_bound_symm (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    (G : ManyBodyOpS (HypercubicTorus d L) N) (w : List Bool)
    (hcond : 3 * (N : ℝ) * ((w.length + w.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    |(star Φ ⬝ᵥ (orderWordProd d L N w * G * orderWordProd d L N w).mulVec Φ).re|
      ≤ 3 / 2 * manyBodyOperatorNormS G * phatMoment d L N Φ w.length := by
  have hbd := renormalized_inserted_product_bound d L N hN Φ hsing hm0 hlro G w w hcond
  have hPnn : 0 ≤ phatMoment d L N Φ w.length := phatMoment_nonneg d L N Φ w.length
  rwa [Real.sqrt_mul_self hPnn] at hbd

/-! ### The single centering step (R2 commit 4) -/

/-- Operator-level append identity for the word product. -/
theorem orderWordProd_mul_append [NeZero L] (w w' : List Bool) :
    orderWordProd d L N (w ++ w')
      = orderWordProd d L N w * orderWordProd d L N w' := by
  simp [orderWordProd, List.map_append, List.prod_append]

/-- A single-letter word product is the corresponding order-density operator. -/
theorem orderWordProd_singleton [NeZero L] (a : Bool) :
    orderWordProd d L N [a] = staggeredOrderDensityOpS d L N a := by
  simp [orderWordProd]

/-- **Single centering step (operator identity).**  Moving the last left letter `a` across the
inserted `G` toward the center splits the sandwich into a more-balanced sandwich with the *same* `G`
plus an error sandwich carrying the decayed commutator `orderComm a G`. -/
theorem inserted_centering_step_eq [NeZero L] (wₗ' wᵣ : List Bool) (a : Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    orderWordProd d L N (wₗ' ++ [a]) * G * orderWordProd d L N wᵣ
      = orderWordProd d L N wₗ' * G * orderWordProd d L N (a :: wᵣ)
        + orderWordProd d L N wₗ' * orderComm a G * orderWordProd d L N wᵣ := by
  rw [orderWordProd_mul_append, orderWordProd_singleton, orderWordProd_mul_cons, orderComm]
  noncomm_ring

/-- **Single centering step (expectation triangle bound).**  The real part of the imbalanced
sandwich expectation is controlled by the more-balanced sandwich plus the decayed-commutator error
sandwich.  Iterating drives `G` to the center (Step B) while accumulating geometrically small
errors. -/
theorem inserted_centering_step_re_le [NeZero L] (wₗ' wᵣ : List Bool) (a : Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    |(star Φ ⬝ᵥ (orderWordProd d L N (wₗ' ++ [a]) * G
          * orderWordProd d L N wᵣ).mulVec Φ).re|
      ≤ |(star Φ ⬝ᵥ (orderWordProd d L N wₗ' * G
            * orderWordProd d L N (a :: wᵣ)).mulVec Φ).re|
        + |(star Φ ⬝ᵥ (orderWordProd d L N wₗ' * orderComm a G
            * orderWordProd d L N wᵣ).mulVec Φ).re| := by
  rw [inserted_centering_step_eq, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  exact abs_add_le _ _

/-! ### Bridging the local-decay class through one centering step (R2 commit 5) -/

/-- A single order-density commutator of a depth-`≥1` local operator decays by `2ζo₀/V`:
`‖orderComm a G‖ ≤ (2ζo₀/V) g₀`. -/
theorem IsR2LocalUpTo.orderComm_norm_le [NeZero L] {K : ℕ} {ζ o₀ g₀ : ℝ}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (h : IsR2LocalUpTo K ζ o₀ g₀ G)
    (a : Bool) (hK : 1 ≤ K) :
    manyBodyOperatorNormS (orderComm a G) ≤ (2 * ζ * o₀) / (L : ℝ) ^ d * g₀ := by
  have hb := h.norm_iter [a] (by simpa using hK)
  simpa [iterOrderComm, pow_one] using hb

/-- **Recursive class membership.**  If `G` is in the local-decay class up to depth `K+1`, then each
order-density commutator `orderComm a G` is in the class up to depth `K` with the decayed constant
`(2ζo₀/V) g₀`.  This drives the split-independent induction: each centering step lowers the depth by
one and contracts the constant geometrically. -/
theorem IsR2LocalUpTo.orderComm_mem [NeZero L] {K : ℕ} {ζ o₀ g₀ : ℝ}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (h : IsR2LocalUpTo (K + 1) ζ o₀ g₀ G)
    (a : Bool) (hdecay : 0 ≤ (2 * ζ * o₀) / (L : ℝ) ^ d) :
    IsR2LocalUpTo K ζ o₀ ((2 * ζ * o₀) / (L : ℝ) ^ d * g₀) (orderComm a G) := by
  refine ⟨mul_nonneg hdecay h.g0_nonneg, ?_⟩
  intro u hu
  have heq : iterOrderComm u (orderComm a G) = iterOrderComm (a :: u) G := rfl
  rw [heq]
  have hb := h.norm_iter (a :: u) (by simp only [List.length_cons]; omega)
  refine le_trans hb (le_of_eq ?_)
  rw [List.length_cons, pow_succ]
  ring

/-- **Mirror centering step (operator identity).**  Moving the first right letter `a` across the
inserted `G` toward the center (from the right side) splits the sandwich into a more-balanced
sandwich with the same `G` minus the decayed-commutator error sandwich. -/
theorem inserted_centering_step_mirror_eq [NeZero L] (wₗ wᵣ' : List Bool) (a : Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    orderWordProd d L N wₗ * G * orderWordProd d L N (a :: wᵣ')
      = orderWordProd d L N (wₗ ++ [a]) * G * orderWordProd d L N wᵣ'
        - orderWordProd d L N wₗ * orderComm a G * orderWordProd d L N wᵣ' := by
  rw [orderWordProd_mul_append, orderWordProd_singleton, orderWordProd_mul_cons, orderComm]
  noncomm_ring

/-- **Mirror centering step (expectation triangle bound).**  The right-side mirror of
`inserted_centering_step_re_le`, used when the inserted `G` lies left of the center. -/
theorem inserted_centering_step_mirror_re_le [NeZero L] (wₗ wᵣ' : List Bool) (a : Bool)
    (G : ManyBodyOpS (HypercubicTorus d L) N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wₗ * G
          * orderWordProd d L N (a :: wᵣ')).mulVec Φ).re|
      ≤ |(star Φ ⬝ᵥ (orderWordProd d L N (wₗ ++ [a]) * G
            * orderWordProd d L N wᵣ').mulVec Φ).re|
        + |(star Φ ⬝ᵥ (orderWordProd d L N wₗ * orderComm a G
            * orderWordProd d L N wᵣ').mulVec Φ).re| := by
  rw [inserted_centering_step_mirror_eq, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  exact abs_sub _ _

/-! ### The unified moment factor and its growth ratio (R2 commit 7) -/

/-- The **unified moment factor** `√(P_{⌊K/2⌋} · P_{⌈K/2⌉})` carried by the split-independent R2
bound: for even `K = 2n` it is `P_n`, for odd `K = 2n+1` it is `√(P_n P_{n+1})`.  This single shape
absorbs the even/odd case distinction in Tasaki's induction. -/
noncomputable def momentFactor (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (K : ℕ) : ℝ :=
  Real.sqrt (phatMoment d L N Φ (K / 2) * phatMoment d L N Φ ((K + 1) / 2))

/-- The moment factor is nonnegative. -/
theorem momentFactor_nonneg (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (K : ℕ) :
    0 ≤ momentFactor d L N Φ K := Real.sqrt_nonneg _

/-- For even `K`, the moment factor collapses to a single moment `P_{K/2}`. -/
theorem momentFactor_two_mul (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n : ℕ) :
    momentFactor d L N Φ (2 * n) = phatMoment d L N Φ n := by
  have h1 : 2 * n / 2 = n := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [momentFactor, h1, h2, Real.sqrt_mul_self (phatMoment_nonneg d L N Φ n)]

/-- **Moment-factor growth ratio (unified, even/odd-free).**  One LRO moment step lifts the moment
factor by `√(2q₀)`: `√(2q₀)·mf(K) ≤ mf(K+1)`.  The proof needs only the single ratio
`2q₀ P_{K/2} ≤ P_{(K/2)+1}` because the shared factor `P_{(K+1)/2}` cancels (`(K+2)/2 = K/2+1`). -/
theorem momentFactor_succ_ge (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (K : ℕ) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hratio : 2 * q₀ * phatMoment d L N Φ (K / 2) ≤ phatMoment d L N Φ (K / 2 + 1)) :
    Real.sqrt (2 * q₀) * momentFactor d L N Φ K ≤ momentFactor d L N Φ (K + 1) := by
  have hidx : (K + 1 + 1) / 2 = K / 2 + 1 := by omega
  set a := phatMoment d L N Φ (K / 2) with ha
  set b := phatMoment d L N Φ ((K + 1) / 2) with hb
  set c := phatMoment d L N Φ (K / 2 + 1) with hc
  have hann : 0 ≤ a := phatMoment_nonneg d L N Φ _
  have hbnn : 0 ≤ b := phatMoment_nonneg d L N Φ _
  rw [momentFactor, momentFactor, hidx, ← ha, ← hb, ← hc,
    ← Real.sqrt_mul (show (0:ℝ) ≤ 2 * q₀ by positivity)]
  apply Real.sqrt_le_sqrt
  have hkey : 2 * q₀ * a * b ≤ b * c := by
    have := mul_le_mul_of_nonneg_right hratio hbnn
    nlinarith [this]
  nlinarith [hkey]

end LatticeSystem.Quantum
