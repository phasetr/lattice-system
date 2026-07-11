import LatticeSystem.Quantum.SpinS.AndersonTowerTelescoping
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality

/-!
# Tasaki §4.2.2 Proposition 4.10: the real-part swap band of the Cartesian order word

This module turns the single-swap **equality** `cartWord_swap_dotProduct_eq`
(`AndersonTowerTelescoping`, Prop 4.10 arc PR-3.2b-ii) into the real-part **band** driving the
`ordered → grouped` contraction (Prop 4.10 arc PR-3.3a).  It is the Cartesian analogue of the
`Bool` swap band of Theorem 4.9 (`orderWordProd_swap_re_diff_le`, `swapChain_re_diff_le`), and it
has three layers:

* the **single adjacent-swap band** `cartWord_swap_re_diff_le`: taking the real part of the
  triple-sum swap identity and bounding it, term by term, by a uniform bound `B` on the shortened
  (charge-removed, length-`M−2`) Cartesian word expectations.  Since the Levi-Civita
  coefficients are **real** (`leviCivita3` valued in `{0, ±1} ⊂ ℂ`), the imaginary-part cancellation
  of the `Bool` swap band is
  unnecessary here — each of the `9·|suf|` terms is bounded by `B`;
* the **branching swap-chain band** `cartWord_swapChain_re_diff_le`: a length-`k` chain of adjacent
  transpositions changes the real expectation by at most `k · 9M · B` — the induction over
  `SwapChain` (now polymorphic, `OrderOperatorAlgebra`) bundling each branching single-swap step;
* the **uniform norm bound** `cartWord_expectation_re_abs_le` supplying the concrete
  `B = (V·N)^{M−2} · ⟨Φ, Φ⟩.re` from operator-norm submultiplicativity `‖ô^{w}‖ ≤ (V·N)^{|w|}`
  (`cartWord_manyBodyOperatorNormS_le`, `stagOpVec_manyBodyOperatorNormS_le`), and the capstone
  `cartWord_swapChain_re_diff_norm_le` instantiating it into a self-contained band.

The self-contained norm scale keeps this step independent of the `(ô²)`-moment lower bound (a
separate arc); the `ordered → grouped` main-part identification and the `doubleFactorial → 1/(M+1)`
reconstruction are the next step (PR-3.3b).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.58)–(4.2.59), p.108; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Reality of the Levi-Civita coefficients -/

/-- The Levi-Civita symbol is real: `(ε_{αβγ}).im = 0`, since its values `{0, ±1}` are real. -/
private theorem leviCivita3_im (a b c : Fin 3) : (leviCivita3 a b c).im = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [leviCivita3]

/-- The Levi-Civita symbol has norm at most one: `‖ε_{αβγ}‖ ≤ 1`, since its values `{0, ±1}` all
have norm at most one. -/
private theorem leviCivita3_norm_le_one (a b c : Fin 3) : ‖leviCivita3 a b c‖ ≤ 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [leviCivita3]

/-- **Real double-coefficient bound.**  For two real scalars `a`, `b` of norm at most one, the real
part of the doubled rotation coefficient `(i a)(i b) z` is dominated by `|z.re|`.  This packages the
single-swap coefficient `(i ε_{αβγ})(i ε_{γ w_k δ})`, which — being real — contributes no imaginary
cross term: `((i a)(i b) z).re = −(a.re · b.re) · z.re`, whence `|·| ≤ |a.re| · |b.re| · |z.re| ≤
|z.re|`. -/
private theorem cart_double_coeff_re_le (a b : ℂ) (ha : a.im = 0) (hb : b.im = 0)
    (hna : ‖a‖ ≤ 1) (hnb : ‖b‖ ≤ 1) (z : ℂ) :
    |((Complex.I * a) * (Complex.I * b) * z).re| ≤ |z.re| := by
  have hc : ((Complex.I * a) * (Complex.I * b)).im = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ha, hb]
  have hcre : ((Complex.I * a) * (Complex.I * b)).re = -(a.re * b.re) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ha, hb]
  rw [Complex.mul_re, hc, zero_mul, sub_zero, hcre, abs_mul, abs_neg, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  have h1 : |a.re| ≤ 1 := le_trans (by simpa using RCLike.abs_re_le_norm a) hna
  have h2 : |b.re| ≤ 1 := le_trans (by simpa using RCLike.abs_re_le_norm b) hnb
  calc |a.re| * |b.re| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-! ### The single adjacent-swap real band -/

/-- **Single adjacent-swap real band** (Prop 4.10 arc PR-3.3a).  Taking the real part of the
single-swap expectation identity `cartWord_swap_dotProduct_eq` and bounding each of its `9·|suf|`
triple-sum terms, one adjacent transposition of a Cartesian order word changes the real expectation
by at most `9·|suf|·B`, where `B` uniformly bounds the real expectations of the shortened
(charge-removed) length-`(|pre|+|suf|)` Cartesian words.  The Levi-Civita coefficients being real,
no `Bool`-style imaginary-part cancellation is needed. -/
theorem cartWord_swap_re_diff_le (A : Λ → Bool) (pre suf : List (Fin 3)) (α β : Fin 3)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) (B : ℝ)
    (hbnd : ∀ u : List (Fin 3), u.length = pre.length + suf.length →
        |(star Φ ⬝ᵥ (cartWord A N u).mulVec Φ).re| ≤ B) :
    |(star Φ ⬝ᵥ (cartWord A N (pre ++ α :: β :: suf)).mulVec Φ).re
        - (star Φ ⬝ᵥ (cartWord A N (pre ++ β :: α :: suf)).mulVec Φ).re|
      ≤ 9 * (suf.length : ℝ) * B := by
  have hbound : ∀ (γ : Fin 3) (k : Fin suf.length) (δ : Fin 3),
      |(((Complex.I * leviCivita3 α β γ) * (Complex.I * leviCivita3 γ (suf.get k) δ))
          * (star Φ ⬝ᵥ (cartWord A N (pre ++ suf.set (k : ℕ) δ)).mulVec Φ)).re| ≤ B := by
    intro γ k δ
    refine le_trans (cart_double_coeff_re_le _ _ (leviCivita3_im _ _ _) (leviCivita3_im _ _ _)
      (leviCivita3_norm_le_one _ _ _) (leviCivita3_norm_le_one _ _ _) _) ?_
    exact hbnd _ (by rw [List.length_append, List.length_set])
  rw [← Complex.sub_re, cartWord_swap_dotProduct_eq A pre suf α β Φ h3 h1]
  simp only [Complex.re_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun γ _ => Finset.abs_sum_le_sum_abs _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun γ _ =>
    Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))) ?_
  refine le_trans (Finset.sum_le_sum (fun γ _ =>
    Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun δ _ => hbound γ k δ)))) ?_
  have hcard : (∑ _γ : Fin 3, ∑ _k : Fin suf.length, ∑ _δ : Fin 3, B)
      = 9 * (suf.length : ℝ) * B := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  exact le_of_eq hcard

/-! ### The branching swap-chain real band -/

/-- **Single adjacent-swap real band, `AdjSwap` form.**  Repackages `cartWord_swap_re_diff_le` for
an `AdjSwap w w'` of a length-`n` word: with `B` uniformly bounding the length-`(n−2)` Cartesian
word expectations, one transposition changes the real expectation by at most `9n·B`. -/
theorem cartWord_adjSwap_re_diff_le (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List (Fin 3), u.length = n - 2 →
        |(star Φ ⬝ᵥ (cartWord A N u).mulVec Φ).re| ≤ B)
    {w w' : List (Fin 3)} (h : AdjSwap w w') (hn : w.length = n) :
    |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (cartWord A N w').mulVec Φ).re|
      ≤ 9 * (n : ℝ) * B := by
  obtain ⟨pre, suf, α, β, rfl, rfl⟩ := h
  simp only [List.length_append, List.length_cons] at hn
  have hbnd' : ∀ u : List (Fin 3), u.length = pre.length + suf.length →
      |(star Φ ⬝ᵥ (cartWord A N u).mulVec Φ).re| ≤ B := by
    intro u hu; exact hbnd u (by rw [hu]; omega)
  refine le_trans (cartWord_swap_re_diff_le A pre suf α β Φ h3 h1 B hbnd') ?_
  have hsufn : (suf.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : suf.length ≤ n)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsufn (by norm_num)) hB

/-- **Branching swap-chain real band** (Prop 4.10 arc PR-3.3a tip, abstract bound).  A length-`k`
chain of adjacent transpositions between length-`n` Cartesian order words changes the real
expectation by at most `k · 9n · B`, where `B` uniformly bounds the length-`(n−2)` Cartesian
word expectations.  Cartesian analogue of `swapChain_re_diff_le` (Theorem 4.9): each branching swap
step contributes `9n·B`, telescoped over the chain. -/
theorem cartWord_swapChain_re_diff_le (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List (Fin 3), u.length = n - 2 →
        |(star Φ ⬝ᵥ (cartWord A N u).mulVec Φ).re| ≤ B)
    {k : ℕ} {w w' : List (Fin 3)} (hc : SwapChain k w w') :
    w.length = n →
      |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re
          - (star Φ ⬝ᵥ (cartWord A N w').mulVec Φ).re|
        ≤ (k : ℝ) * (9 * n * B) := by
  induction hc with
  | refl w => intro _; simp
  | @step j w w' w'' hs hchain ih =>
    intro hn
    have hw'n : w'.length = n := by rw [← hs.length_eq]; exact hn
    have hstep := cartWord_adjSwap_re_diff_le A Φ h3 h1 n B hB hbnd hs hn
    have ih' := ih hw'n
    calc |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re
            - (star Φ ⬝ᵥ (cartWord A N w'').mulVec Φ).re|
        ≤ |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re
              - (star Φ ⬝ᵥ (cartWord A N w').mulVec Φ).re|
          + |(star Φ ⬝ᵥ (cartWord A N w').mulVec Φ).re
              - (star Φ ⬝ᵥ (cartWord A N w'').mulVec Φ).re| := abs_sub_le _ _ _
      _ ≤ 9 * n * B + (j : ℝ) * (9 * n * B) := add_le_add hstep ih'
      _ = ((j : ℝ) + 1) * (9 * n * B) := by ring
      _ = ((j + 1 : ℕ) : ℝ) * (9 * n * B) := by push_cast; ring

/-! ### The uniform operator-norm bound and the concrete band -/

/-- **Uniform axis-operator norm bound** `‖ô^{(α)}‖ ≤ V·N`.  Each staggered axis operator is a
`±1`-signed sum of the `V` per-site spin operators, whose norms are at most `N`
(`onSiteS_spinSOp{1,2,3}_manyBodyOperatorNormS_le`); the triangle inequality gives the extensive
bound uniformly in the axis `α`. -/
theorem stagOpVec_manyBodyOperatorNormS_le (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) (α : Fin 3) :
    manyBodyOperatorNormS (stagOpVec A N α) ≤ (Fintype.card Λ : ℝ) * N := by
  have hbound : ∀ (S : Λ → ManyBodyOpS Λ N), (∀ x, manyBodyOperatorNormS (S x) ≤ (N : ℝ)) →
      manyBodyOperatorNormS (∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • S x)
        ≤ (Fintype.card Λ : ℝ) * N := by
    intro S hS
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    calc ∑ x : Λ, manyBodyOperatorNormS ((if A x then (1 : ℂ) else (-1 : ℂ)) • S x)
        ≤ ∑ _x : Λ, (N : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [manyBodyOperatorNormS_smul,
            show ‖(if A x then (1 : ℂ) else (-1 : ℂ))‖ = 1 by split_ifs <;> simp, one_mul]
          exact hS x
      _ = (Fintype.card Λ : ℝ) * N := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  fin_cases α <;> simp only [stagOpVec]
  · rw [staggeredOrderOp1S]
    exact hbound _ (fun x => onSiteS_spinSOp1_manyBodyOperatorNormS_le x hN)
  · rw [staggeredOrderOp2S]
    exact hbound _ (fun x => onSiteS_spinSOp2_manyBodyOperatorNormS_le x hN)
  · rw [staggeredOrderOpS]
    exact hbound _ (fun x => le_trans (onSiteS_spinSOp3_manyBodyOperatorNormS_le x) (by linarith))

/-- **Cartesian word norm bound** `‖ô^{w}‖ ≤ (V·N)^{|w|}`: submultiplicativity of the operator norm
over the ordered product, each letter contributing the uniform axis bound `‖ô^{(α)}‖ ≤ V·N`
(`stagOpVec_manyBodyOperatorNormS_le`). -/
theorem cartWord_manyBodyOperatorNormS_le (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) (w : List (Fin 3)) :
    manyBodyOperatorNormS (cartWord A N w) ≤ ((Fintype.card Λ : ℝ) * N) ^ w.length := by
  induction w with
  | nil =>
    simp only [cartWord, List.map_nil, List.prod_nil, List.length_nil, pow_zero]
    rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_one]; simp
  | cons a t ih =>
    rw [cartWord_cons, List.length_cons]
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    calc manyBodyOperatorNormS (stagOpVec A N a) * manyBodyOperatorNormS (cartWord A N t)
        ≤ ((Fintype.card Λ : ℝ) * N) * ((Fintype.card Λ : ℝ) * N) ^ t.length :=
          mul_le_mul (stagOpVec_manyBodyOperatorNormS_le A N hN a) ih
            (manyBodyOperatorNormS_nonneg _) (by positivity)
      _ = ((Fintype.card Λ : ℝ) * N) ^ (t.length + 1) := by rw [pow_succ']

/-- The self-pairing real part equals the squared Euclidean norm: `⟨Φ, Φ⟩.re = ‖Φ‖²₂`. -/
private theorem re_star_dotProduct_self_eq (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star Φ ⬝ᵥ Φ).re
      = ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by
  have h := inner_self_eq_norm_mul_norm (𝕜 := ℂ)
    (WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm] at h
  simpa using h

/-- **Uniform real-expectation norm bound** `|⟨Φ, ô^{w} Φ⟩.re| ≤ (V·N)^{|w|} · ⟨Φ, Φ⟩.re`.
Combining
the operator Cauchy–Schwarz bound (`abs_re_dotProduct_mulVec_le_norm_mul`) with the Cartesian word
norm bound (`cartWord_manyBodyOperatorNormS_le`); the self-contained scale needed to discharge the
uniform bound `B` of the swap-chain band. -/
theorem cartWord_expectation_re_abs_le (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) (w : List (Fin 3))
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re|
      ≤ ((Fintype.card Λ : ℝ) * N) ^ w.length * (star Φ ⬝ᵥ Φ).re := by
  have hb := abs_re_dotProduct_mulVec_le_norm_mul (cartWord A N w) Φ Φ
  rw [mul_assoc, ← re_star_dotProduct_self_eq Φ] at hb
  refine le_trans hb ?_
  refine mul_le_mul_of_nonneg_right (cartWord_manyBodyOperatorNormS_le A N hN w) ?_
  rw [re_star_dotProduct_self_eq]; positivity

/-- **Concrete branching swap-chain band** (Prop 4.10 arc PR-3.3a capstone).  Instantiating the
abstract band `cartWord_swapChain_re_diff_le` with the self-contained operator-norm scale
`B = (V·N)^{n−2} · ⟨Φ, Φ⟩.re` (`cartWord_expectation_re_abs_le`): a length-`k` swap chain between
length-`n` Cartesian order words changes the real expectation by at most
`k · 9n · (V·N)^{n−2} · ⟨Φ, Φ⟩.re`.  This is the `ordered → grouped` real band consumed by the
main-part identification (PR-3.3b). -/
theorem cartWord_swapChain_re_diff_norm_le (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) (n : ℕ) {k : ℕ} {w w' : List (Fin 3)}
    (hc : SwapChain k w w') (hn : w.length = n) :
    |(star Φ ⬝ᵥ (cartWord A N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (cartWord A N w').mulVec Φ).re|
      ≤ (k : ℝ) * (9 * n
          * (((Fintype.card Λ : ℝ) * N) ^ (n - 2) * (star Φ ⬝ᵥ Φ).re)) := by
  have hΦnn : (0 : ℝ) ≤ (star Φ ⬝ᵥ Φ).re := by
    rw [re_star_dotProduct_self_eq]; positivity
  refine cartWord_swapChain_re_diff_le A Φ h3 h1 n
    (((Fintype.card Λ : ℝ) * N) ^ (n - 2) * (star Φ ⬝ᵥ Φ).re)
    (mul_nonneg (by positivity) hΦnn) ?_ hc hn
  intro u hu
  have hbnd := cartWord_expectation_re_abs_le A N hN u Φ
  rwa [hu] at hbnd

end LatticeSystem.Quantum
