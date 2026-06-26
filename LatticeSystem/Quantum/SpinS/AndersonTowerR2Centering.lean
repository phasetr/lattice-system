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

end LatticeSystem.Quantum
