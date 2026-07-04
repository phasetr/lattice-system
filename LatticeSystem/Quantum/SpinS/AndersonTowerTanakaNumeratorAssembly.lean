/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), crux sub-arc PR-D — the numerator
assembly (the `1`-axis binomial cancellation, Tasaki eqs. (4.2.68)/(4.2.71)).

The Anderson-tower numerator for the `1`-axis order operator is, after the scale-invariance drop
(`tanakaTowerTerm_expectationRatioRe_eq`, eq. (4.2.70)), the double commutator
`⟨Φ, [Ã^M, [Ĥ, Ã^M]] Φ⟩` of the summed order density `Ã = ô⁺ + ô⁻`.  The double telescoping
identity (eq. (4.2.71), `double_commutator_pow_eq_double_sum`) rewrites it as the `M²`-fold sum,
over insertion positions `j, l < M`, of the single physical double commutator
`d̃ = [Ã, [Ĥ, Ã]] = orderDensitySumDoubleComm` sandwiched between powers of `Ã`.  This file bounds
that sum in three layers:

* **per-piece** (`numTerm_piece_bound`): for a *charge-homogeneous* middle operator `G` of the
  local-decay class, expand the two surrounding powers `Ã^a, Ã^b` into order words; the singlet
  charge-selection rule (`dotProduct_word_sandwich_eq_zero_of_charge_ne`) kills every word-pair
  whose combined `true`-count differs from the resonant `tt`, and each surviving pair is bounded by
  the split-independent leaf bound (eq. (4.2.68), `r2_split_independent`) as `≤ 3 g₀ P_{M-1}`.  The
  surviving pairs number `C(a+b, tt) ≤ C(2(M-1), M-1)` (`card_pair_count_true_eq` +
  `Nat.choose_le_middle`).
* **per-charge-piece double sum** (`numPiece_double_sum_bound`): summing the per-piece bound over
  the `M²` telescoping positions gives the factor `M²`.
* **assembly** (`tanaka_numerator_bound`): the four charge pieces `G₊, [ô⁺,[Ĥ,ô⁻]], [ô⁻,[Ĥ,ô⁺]], G₋`
  (`orderDensitySumDoubleComm_eq_charge_pieces`), each in the local-decay class with aggregate
  `≤ 96 d N⁴ / V`, are combined.

The central binomial `C(2(M-1), M-1)` produced here is one half of the Pascal ratio
`C(2M-2, M-1)/C(2M, M) = M/(2(2M-1))` whose cancellation against the denominator's `C(2M, M)`
(`orderSum_pow_two_denom_lower`, PR-B) drives the crux; that cancellation is assembled in the
capstone PR-E.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.67)–(4.2.71), pp. 111–112 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaNumeratorCore
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaDenominator
import LatticeSystem.Math.CommutatorTelescope
import Mathlib.Logic.Equiv.Fin.Basic

namespace LatticeSystem.Quantum

open Matrix

/-! ### Counting the resonant word pairs -/

/-- **Pair-word counting**: the number of pairs `(cl, cr)` (`cl : Fin a → Bool`,
`cr : Fin b → Bool`) whose combined `true`-count is exactly `t` equals `C(a + b, t)`.  The
concatenation equivalence `Fin.appendEquiv` identifies such a pair with a single length-`(a + b)`
word of `true`-count `t` (`List.ofFn_fin_append` + `List.count_append`), whose count is
`card_ofFn_count_true_eq`. -/
theorem card_pair_count_true_eq (a b t : ℕ) :
    (Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
        (List.ofFn p.1).count true + (List.ofFn p.2).count true = t)).card
      = (a + b).choose t := by
  rw [← card_ofFn_count_true_eq (a + b) t]
  refine Finset.card_equiv (Fin.appendEquiv a b) (fun p => ?_)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have he : (Fin.appendEquiv a b) p = Fin.append p.1 p.2 := rfl
  rw [he, List.ofFn_fin_append, List.count_append]

/-! ### Per-piece numerator bound (eq. (4.2.68) reused word-generically) -/

/-- **Per-piece numerator bound** (eqs. (4.2.68)/(4.2.71)).  For a charge-`γ` homogeneous middle
operator `G` (`[Ŝ_tot^{(3)}, G] = γ G`) of the local-decay class up to depth `2n`, inserted between
powers `Ã^a, Ã^b` of the summed order density with `a + b = 2n`, on a `Ŝ_tot^{(3)}`-singlet `Φ`:
`|Re⟨Φ, Ã^a G Ã^b Φ⟩| ≤ C(2n, n) · 3 g₀ P_n`.

Proof: expand `Ã^a, Ã^b` into order words (`orderDensitySum_pow_eq_sum_words`); the cross-charge
selection rule kills every word-pair whose combined `true`-count differs from the resonant `tt`
(`hsel`), and each surviving pair is bounded by the split-independent leaf bound (eq. (4.2.68),
`r2_split_independent`, `momentFactor_two_mul`) as `≤ 3 g₀ P_n`.  The surviving pairs number
`C(a + b, tt) ≤ C(2n, n)` (`card_pair_count_true_eq`, `Nat.choose_le_middle`). -/
theorem numTerm_piece_bound (d L N n : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ ζ o₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ m, 2 * q₀ * phatMoment d L N Φ m ≤ phatMoment d L N Φ (m + 1))
    (hdecay : 0 ≤ (2 * ζ * o₀) / (L : ℝ) ^ d)
    (hcond : 3 * (N : ℝ) * ((2 * n : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * n : ℕ) : ℝ)
        * ((2 * ζ * o₀) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (G : ManyBodyOpS (HypercubicTorus d L) N) (γ : ℂ)
    (hG : totalSpinSOp3 (HypercubicTorus d L) N * G - G * totalSpinSOp3 (HypercubicTorus d L) N
        = γ • G)
    (g₀ : ℝ) (hcls : IsR2LocalUpTo (2 * n) ζ o₀ g₀ G) (tt a b : ℕ) (hab : a + b = 2 * n)
    (hsel : ∀ (cl : Fin a → Bool) (cr : Fin b → Bool),
        mCharge (List.ofFn cl) + γ + mCharge (List.ofFn cr) = 0 →
        (List.ofFn cl).count true + (List.ofFn cr).count true = tt) :
    |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ a * G
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ b).mulVec Φ).re|
      ≤ ((2 * n).choose n : ℝ) * (3 * g₀ * phatMoment d L N Φ n) := by
  have hg0nn := hcls.g0_nonneg
  have hPnn := phatMoment_nonneg d L N Φ n
  have hconstnn : (0 : ℝ) ≤ 3 * g₀ * phatMoment d L N Φ n :=
    mul_nonneg (mul_nonneg (by norm_num) hg0nn) hPnn
  have hop : (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ a * G
        * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ b
      = ∑ p : (Fin a → Bool) × (Fin b → Bool),
          orderWordProd d L N (List.ofFn p.1) * G * orderWordProd d L N (List.ofFn p.2) := by
    rw [orderDensitySum_pow_eq_sum_words d L N a, orderDensitySum_pow_eq_sum_words d L N b,
      Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun cl _ => ?_)
    rw [Finset.mul_sum]
  rw [hop, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  have hsub : (∑ p : (Fin a → Bool) × (Fin b → Bool),
        (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1) * G
          * orderWordProd d L N (List.ofFn p.2)).mulVec Φ).re)
      = ∑ p ∈ Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
          (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt),
          (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1) * G
            * orderWordProd d L N (List.ofFn p.2)).mulVec Φ).re := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun p _ hp => ?_)).symm
    rw [Finset.mem_filter, not_and] at hp
    have hne := hp (Finset.mem_univ p)
    exact dotProduct_word_sandwich_eq_zero_of_charge_ne d L N Φ hsing
      (List.ofFn p.1) (List.ofFn p.2) G γ hG (fun hz => hne (hsel p.1 p.2 hz))
  rw [hsub]
  have hbound : ∀ p ∈ Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
        (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt),
      |(star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1) * G
          * orderWordProd d L N (List.ofFn p.2)).mulVec Φ).re|
        ≤ 3 * g₀ * phatMoment d L N Φ n := by
    intro p _
    have hr := r2_split_independent d L N hN Φ hsing hq₀ hm0 hratio hdecay (2 * n) hcond hbudget
      (List.ofFn p.1) (List.ofFn p.2) G g₀
      (by rw [List.length_ofFn, List.length_ofFn]; exact hab) hcls
    rwa [momentFactor_two_mul] at hr
  calc |∑ p ∈ Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
          (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt),
        (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1) * G
          * orderWordProd d L N (List.ofFn p.2)).mulVec Φ).re|
      ≤ ∑ p ∈ Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
          (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt),
          |(star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1) * G
            * orderWordProd d L N (List.ofFn p.2)).mulVec Φ).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
          (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt),
          (3 * g₀ * phatMoment d L N Φ n) := Finset.sum_le_sum hbound
    _ = ((Finset.univ.filter (fun p : (Fin a → Bool) × (Fin b → Bool) =>
          (List.ofFn p.1).count true + (List.ofFn p.2).count true = tt)).card : ℝ)
          * (3 * g₀ * phatMoment d L N Φ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * n).choose n : ℝ) * (3 * g₀ * phatMoment d L N Φ n) := by
        refine mul_le_mul_of_nonneg_right ?_ hconstnn
        rw [card_pair_count_true_eq a b tt, hab]
        have hmid : (2 * n).choose tt ≤ (2 * n).choose n := by
          have h := Nat.choose_le_middle tt (2 * n)
          rwa [show 2 * n / 2 = n from by omega] at h
        exact_mod_cast hmid

/-! ### The `M²` telescoping double sum over one charge piece -/

/-- **Per-charge-piece double-sum bound** (eq. (4.2.71)): summing the per-piece bound
(`numTerm_piece_bound`) over the `M²` telescoping positions `j, l < M` yields the factor `M²`.  For
a charge-`γ` homogeneous middle operator `G` of the local-decay class up to depth `2(M-1)` whose
resonant `true`-count is `tt`:
`|Re⟨Φ, Σ_{j,l<M} Ã^{j+l} G Ã^{2(M-1)-j-l} Φ⟩| ≤ M² · C(2(M-1), M-1) · 3 g₀ P_{M-1}`. -/
theorem numPiece_double_sum_bound (d L N M : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ ζ o₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ m, 2 * q₀ * phatMoment d L N Φ m ≤ phatMoment d L N Φ (m + 1))
    (hdecay : 0 ≤ (2 * ζ * o₀) / (L : ℝ) ^ d)
    (hcond : 3 * (N : ℝ) * ((2 * (M - 1) : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * (M - 1) : ℕ) : ℝ)
        * ((2 * ζ * o₀) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (G : ManyBodyOpS (HypercubicTorus d L) N) (γ : ℂ)
    (hG : totalSpinSOp3 (HypercubicTorus d L) N * G - G * totalSpinSOp3 (HypercubicTorus d L) N
        = γ • G)
    (g₀ : ℝ) (hcls : IsR2LocalUpTo (2 * (M - 1)) ζ o₀ g₀ G) (tt : ℕ)
    (hsel : ∀ (a b : ℕ), a + b = 2 * (M - 1) → ∀ (cl : Fin a → Bool) (cr : Fin b → Bool),
        mCharge (List.ofFn cl) + γ + mCharge (List.ofFn cr) = 0 →
        (List.ofFn cl).count true + (List.ofFn cr).count true = tt) :
    |(star Φ ⬝ᵥ (∑ j ∈ Finset.range M, ∑ l ∈ Finset.range M,
        (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ (j + l) * G
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)).mulVec Φ).re|
      ≤ (M : ℝ) ^ 2 * ((2 * (M - 1)).choose (M - 1) : ℝ)
          * (3 * g₀ * phatMoment d L N Φ (M - 1)) := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  calc |∑ j ∈ Finset.range M, ∑ l ∈ Finset.range M,
          (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (j + l) * G
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)).mulVec Φ).re|
      ≤ ∑ j ∈ Finset.range M, |∑ l ∈ Finset.range M,
          (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (j + l) * G
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)).mulVec Φ).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range M, ∑ l ∈ Finset.range M,
          |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (j + l) * G
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)).mulVec Φ).re| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range M, ∑ l ∈ Finset.range M,
          ((2 * (M - 1)).choose (M - 1) : ℝ) * (3 * g₀ * phatMoment d L N Φ (M - 1)) :=
        Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun l hl => by
          have hj' := Finset.mem_range.mp hj
          have hl' := Finset.mem_range.mp hl
          exact numTerm_piece_bound d L N (M - 1) hN Φ hsing hq₀ hm0 hratio hdecay hcond hbudget
            G γ hG g₀ hcls tt (j + l) (2 * (M - 1) - j - l) (by omega)
            (hsel (j + l) (2 * (M - 1) - j - l) (by omega))))
    _ = (M : ℝ) ^ 2 * ((2 * (M - 1)).choose (M - 1) : ℝ)
          * (3 * g₀ * phatMoment d L N Φ (M - 1)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### Resonant `true`-count from a vanishing charge (bridge `mCharge` → letter counts) -/

/-- **Resonant count from charge cancellation.**  On a word pair `(cl, cr)` of lengths summing to
`2n`, if the combined `Ŝ_tot^{(3)}`-charge `m(cl) + γ + m(cr)` vanishes (`γ` an integer charge, with
integer witness `γz`), then the combined `true`-count is pinned by `2 S = 2n − γz`.  Bridges the
complex `mCharge` (`mCharge_eq_count`) to the integer letter counts (`count_true_add_count_false`),
then `omega`. -/
private theorem count_of_charge_zero (a b : ℕ) (cl : Fin a → Bool) (cr : Fin b → Bool)
    (γ : ℂ) (γz : ℤ) (hγ : (γz : ℂ) = γ) (n : ℕ) (hab : a + b = 2 * n)
    (hz : mCharge (List.ofFn cl) + γ + mCharge (List.ofFn cr) = 0) :
    2 * (((List.ofFn cl).count true : ℤ) + ((List.ofFn cr).count true : ℤ))
      = 2 * (n : ℤ) - γz := by
  rw [← hγ, mCharge_eq_count, mCharge_eq_count] at hz
  have hlen1 : (List.ofFn cl).count true + (List.ofFn cl).count false = a := by
    have h := count_true_add_count_false (List.ofFn cl); rwa [List.length_ofFn] at h
  have hlen2 : (List.ofFn cr).count true + (List.ofFn cr).count false = b := by
    have h := count_true_add_count_false (List.ofFn cr); rwa [List.length_ofFn] at h
  have hZ : (((List.ofFn cl).count true : ℤ) - ((List.ofFn cl).count false : ℤ))
        + γz + (((List.ofFn cr).count true : ℤ) - ((List.ofFn cr).count false : ℤ)) = 0 := by
    exact_mod_cast hz
  omega

/-! ### The numerator upper bound (Tasaki eqs. (4.2.70)/(4.2.71)) -/

/-- **Tanaka numerator upper bound** ([N2], eqs. (4.2.70)/(4.2.71)).  On a `Ŝ_tot^{(3)}`-singlet `Φ`
(eq. (4.1.7)) whose order moments satisfy the long-range-order ratio `2 q₀ P_n ≤ P_{n+1}`, under the
size conditions `hcond`/`hbudget`, the Anderson-tower numerator (the `1`-axis double commutator
`[Ã^M, [Ĥ, Ã^M]]`, `Ã = ô⁺ + ô⁻`) obeys
`|Re⟨Φ, [Ã^M, [Ĥ, Ã^M]] Φ⟩| ≤ M² · C(2(M-1), M-1) · 12 · (96 d N⁴ / V) · P_{M-1}`.

Proof: double-telescope the numerator (eq. (4.2.71), `double_commutator_pow_eq_double_sum`) into
`M²` insertions of `d̃ = orderDensitySumDoubleComm`; split `d̃` into its four charge pieces
(`orderDensitySumDoubleComm_eq_charge_pieces`), each charge homogeneous and in the local-decay class
with aggregate `≤ 96 d N⁴ / V`; bound each piece's `M²`-fold sum by `numPiece_double_sum_bound`.
The
central binomial `C(2(M-1), M-1)` produced here is half the Pascal ratio cancelled against the
denominator in the capstone PR-E. -/
theorem tanaka_numerator_bound (d L N : ℕ) [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ m, 2 * q₀ * phatMoment d L N Φ m ≤ phatMoment d L N Φ (m + 1)) (M : ℕ) (hM : 1 ≤ M)
    (hcond : 3 * (N : ℝ) * ((2 * (M - 1) : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * (M - 1) : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ M
          * (heisenbergHamiltonianS (torusNNCoupling d L) N
              * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ M
            - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ M
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - (heisenbergHamiltonianS (torusNNCoupling d L) N
              * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ M
            - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ M
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ M).mulVec Φ).re|
      ≤ (M : ℝ) ^ 2 * ((2 * (M - 1)).choose (M - 1) : ℝ)
          * (12 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * phatMoment d L N Φ (M - 1)) := by
  have hdecay : (0 : ℝ) ≤ (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d := by positivity
  have hP := phatMoment_nonneg d L N Φ (M - 1)
  have hMC : (0 : ℝ) ≤ (M : ℝ) ^ 2 * ((2 * (M - 1)).choose (M - 1) : ℝ) := by positivity
  rw [double_commutator_pow_eq_double_sum
    (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
    (heisenbergHamiltonianS (torusNNCoupling d L) N) M]
  have hmid : (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
        * (heisenbergHamiltonianS (torusNNCoupling d L) N
            * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
          - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      - (heisenbergHamiltonianS (torusNNCoupling d L) N
            * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
          - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
      = orderDoubleCommSameSign d L N true + orderDoubleComm d L N
        + orderDoubleCommMirror d L N + orderDoubleCommSameSign d L N false := by
    have h := orderDensitySumDoubleComm_eq_charge_pieces d L N
    simpa only [orderDensitySumDoubleComm] using h
  simp only [hmid]
  have hsplit : ∀ j l : ℕ, (staggeredOrderDensityOpS d L N true
        + staggeredOrderDensityOpS d L N false) ^ (j + l)
      * (orderDoubleCommSameSign d L N true + orderDoubleComm d L N
        + orderDoubleCommMirror d L N + orderDoubleCommSameSign d L N false)
      * (staggeredOrderDensityOpS d L N true
        + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)
    = (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ (j + l)
        * orderDoubleCommSameSign d L N true
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)
      + (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ (j + l)
        * orderDoubleComm d L N
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)
      + (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ (j + l)
        * orderDoubleCommMirror d L N
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l)
      + (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ (j + l)
        * orderDoubleCommSameSign d L N false
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * (M - 1) - j - l) :=
    fun j l => by noncomm_ring
  simp only [hsplit, Finset.sum_add_distrib]
  have hlin : ∀ A B : ManyBodyOpS (HypercubicTorus d L) N,
      (star Φ ⬝ᵥ (A + B).mulVec Φ).re
        = (star Φ ⬝ᵥ A.mulVec Φ).re + (star Φ ⬝ᵥ B.mulVec Φ).re := fun A B => by
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  rw [hlin, hlin, hlin]
  -- charge homogeneity of the four pieces
  have hG1 : totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleCommSameSign d L N true
      - orderDoubleCommSameSign d L N true * totalSpinSOp3 (HypercubicTorus d L) N
      = (2 : ℂ) • orderDoubleCommSameSign d L N true := by
    simpa using totalSpinSOp3_commutator_orderDoubleCommSameSign d L N true
  have hG2 : totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleComm d L N
      - orderDoubleComm d L N * totalSpinSOp3 (HypercubicTorus d L) N
      = (0 : ℂ) • orderDoubleComm d L N := by
    rw [zero_smul]; exact totalSpinSOp3_commutator_orderDoubleComm d L N
  have hG3 : totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleCommMirror d L N
      - orderDoubleCommMirror d L N * totalSpinSOp3 (HypercubicTorus d L) N
      = (0 : ℂ) • orderDoubleCommMirror d L N := by
    rw [zero_smul]; exact totalSpinSOp3_commutator_orderDoubleCommMirror d L N
  have hG4 : totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleCommSameSign d L N false
      - orderDoubleCommSameSign d L N false * totalSpinSOp3 (HypercubicTorus d L) N
      = (-2 : ℂ) • orderDoubleCommSameSign d L N false := by
    simpa using totalSpinSOp3_commutator_orderDoubleCommSameSign d L N false
  -- resonant-count selection for each piece
  have hsel1 : ∀ (a b : ℕ), a + b = 2 * (M - 1) → ∀ (cl : Fin a → Bool) (cr : Fin b → Bool),
      mCharge (List.ofFn cl) + (2 : ℂ) + mCharge (List.ofFn cr) = 0 →
      (List.ofFn cl).count true + (List.ofFn cr).count true = M - 2 := by
    intro a b hab cl cr hz
    have h := count_of_charge_zero a b cl cr (2 : ℂ) 2 (by norm_num) (M - 1) hab hz
    omega
  have hsel2 : ∀ (a b : ℕ), a + b = 2 * (M - 1) → ∀ (cl : Fin a → Bool) (cr : Fin b → Bool),
      mCharge (List.ofFn cl) + (0 : ℂ) + mCharge (List.ofFn cr) = 0 →
      (List.ofFn cl).count true + (List.ofFn cr).count true = M - 1 := by
    intro a b hab cl cr hz
    have h := count_of_charge_zero a b cl cr (0 : ℂ) 0 (by norm_num) (M - 1) hab hz
    omega
  have hsel4 : ∀ (a b : ℕ), a + b = 2 * (M - 1) → ∀ (cl : Fin a → Bool) (cr : Fin b → Bool),
      mCharge (List.ofFn cl) + (-2 : ℂ) + mCharge (List.ofFn cr) = 0 →
      (List.ofFn cl).count true + (List.ofFn cr).count true = M := by
    intro a b hab cl cr hz
    have h := count_of_charge_zero a b cl cr (-2 : ℂ) (-2) (by norm_num) (M - 1) hab hz
    omega
  -- the four per-piece double-sum bounds, aggregated to `96 d N⁴ / V`
  have hb1 := numPiece_double_sum_bound d L N M hN Φ hsing hq₀ hm0 hratio hdecay hcond hbudget
    (orderDoubleCommSameSign d L N true) (2 : ℂ) hG1 (orderDoubleCommSameSignAggregate d L N true)
    (isR2LocalUpTo_orderDoubleCommSameSign hL hN true (2 * (M - 1))) (M - 2) hsel1
  have hb2 := numPiece_double_sum_bound d L N M hN Φ hsing hq₀ hm0 hratio hdecay hcond hbudget
    (orderDoubleComm d L N) (0 : ℂ) hG2 (orderDoubleCommAggregate d L N)
    (isR2LocalUpTo_orderDoubleComm hL hN (2 * (M - 1))) (M - 1) hsel2
  have hb3 := numPiece_double_sum_bound d L N M hN Φ hsing hq₀ hm0 hratio hdecay hcond hbudget
    (orderDoubleCommMirror d L N) (0 : ℂ) hG3 (orderDoubleCommMirrorAggregate d L N)
    (isR2LocalUpTo_orderDoubleCommMirror hL hN (2 * (M - 1))) (M - 1) hsel2
  have hb4 := numPiece_double_sum_bound d L N M hN Φ hsing hq₀ hm0 hratio hdecay hcond hbudget
    (orderDoubleCommSameSign d L N false) (-2 : ℂ) hG4
    (orderDoubleCommSameSignAggregate d L N false)
    (isR2LocalUpTo_orderDoubleCommSameSign hL hN false (2 * (M - 1))) M hsel4
  have hY1 := hb1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderDoubleCommSameSignAggregate_le hL hN true) (by norm_num)) hP)
    hMC)
  have hY2 := hb2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderDoubleCommAggregate_le hL hN) (by norm_num)) hP) hMC)
  have hY3 := hb3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderDoubleCommMirrorAggregate_le hL hN) (by norm_num)) hP) hMC)
  have hY4 := hb4.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderDoubleCommSameSignAggregate_le hL hN false) (by norm_num)) hP)
    hMC)
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hY1 hY2)) hY3)) hY4) |>.trans
    (le_of_eq ?_)
  ring

end LatticeSystem.Quantum
