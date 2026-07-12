import LatticeSystem.Quantum.SpinS.AndersonTowerCartWordReBand
import LatticeSystem.Quantum.SpinS.AndersonTowerGroupedNormalForm
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSq
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment
import LatticeSystem.Math.Combinatorics.MultinomialFiber
import LatticeSystem.Math.Combinatorics.PinchCoeff
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Tasaki §4.2.2 Proposition 4.10: the pinch scalar band identity

This module is the algebraic capstone of the Proposition 4.10 (Tasaki §4.2.2, p. 108) pinch arc
(PR-3.3b).  It combines the operator polynomial expansion of the sphere average
(`sphereAverage_directionStaggeredOp_pow`, PR-2), the `ordered → grouped` real band
(`cartWord_swapChain_re_diff_norm_le`, PR-3.3a), the grouped-normal-form swap chains
(`ofFn_swapChain_groupedFin3`, PR-3.3b-α), the multinomial fibre cardinality
(`card_ofFn_count_eq`, PR-3.3b-β) and the coefficient match
(`pinch_coeff_match`, PR-3.3b-γ) into the **scalar band identity**

`|⟨Φ, (∫_{S²} (Ô_L^n)^{2m} dσ) Φ⟩.re − (4π/(2m+1)) ⟨Φ, (ô²)^m Φ⟩.re|
    ≤ cartPinchPoly m · (V·N)^{2m−2} · ⟨Φ, Φ⟩.re`,

expressing the sphere average of the direction order operator as the rotationally invariant main
part `(4π/(2m+1)) (ô²)^m` up to an `O((V·N)^{2m−2})` remainder (Tasaki eqs. (4.2.58)/(4.2.59)).  The
main part is closed by grouping both the ordered and the squared configurations into their grouped
normal form and matching per-configuration coefficients via the double-factorial identity; the
remainder is aggregated from the self-contained operator-norm band of PR-3.3a.  Conjecture 4.12 and
the `(ô²)`-moment lower bound are deferred to later steps (PR-4/PR-5).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.58)–(4.2.60), p. 108.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory LatticeSystem.Math
open scoped Matrix.Norms.Frobenius Nat

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Configuration grouping into the multinomial-weighted normal-form sum -/

/-- **Configuration grouping** (Prop 4.10 pinch bookkeeping).  For any scalar functional `ψ` of a
`Fin 3` count vector, summing `ψ (count word)` over all length-`n` axis configurations
`F : Fin n → Fin 3` equals the multinomial-weighted sum over count vectors `k` summing to `n`:
`∑_F ψ(count F) = ∑_{∑ k = n} multinomial(k) · ψ(k)`.  The configurations are grouped by their
count vector (`Finset.sum_comp`); each count vector summing to `n` is realised (the multinomial
fibre is non-empty by `Nat.multinomial_pos`), and the fibre cardinality is the multinomial
coefficient (`card_ofFn_count_eq`, PR-3.3b-β). -/
private lemma config_sum_eq_multinomial_sum {n : ℕ} (ψ : (Fin 3 → ℕ) → ℝ) :
    ∑ F : Fin n → Fin 3, ψ (fun α => (List.ofFn F).count α)
      = ∑ k ∈ Finset.Nat.antidiagonalTuple 3 n,
          (Nat.multinomial Finset.univ k : ℝ) * ψ k := by
  have himg : (Finset.univ.image
        (fun F : Fin n → Fin 3 => (fun α => (List.ofFn F).count α)))
      = Finset.Nat.antidiagonalTuple 3 n := by
    apply Finset.Subset.antisymm
    · intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨F, -, rfl⟩ := hb
      rw [Finset.Nat.mem_antidiagonalTuple]
      show ∑ i, (List.ofFn F).count i = n
      simp_rw [LatticeSystem.Math.count_ofFn_eq_card_filter F]
      rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (F j)),
        Finset.card_univ, Fintype.card_fin]
    · intro b hb
      rw [Finset.Nat.mem_antidiagonalTuple] at hb
      rw [Finset.mem_image]
      obtain ⟨F, hF⟩ := Finset.card_pos.mp
        (lt_of_lt_of_eq (Nat.multinomial_pos Finset.univ b)
          (LatticeSystem.Math.card_ofFn_count_eq n b hb).symm)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
      exact ⟨F, Finset.mem_univ _, funext (fun α => hF α)⟩
  rw [Finset.sum_comp (fun k => ψ k) (fun F : Fin n → Fin 3 => (fun α => (List.ofFn F).count α)),
    himg]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.Nat.mem_antidiagonalTuple] at hb
  rw [nsmul_eq_mul]
  congr 1
  rw [← LatticeSystem.Math.card_ofFn_count_eq n b hb]
  norm_cast
  congr 1
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-! ### The squared order operator as a sum of doubled Cartesian words -/

/-- The **square word** of an axis configuration `g : Fin m → Fin 3`: the length-`2m` word obtained
by repeating each letter of `List.ofFn g` twice, `(g₀, g₀, g₁, g₁, …)`.  Its Cartesian order-word
product is the ordered product of the squared axis operators `∏_j (ô^{(g j)})²`
(`cartWord_sqWord`), the summand of `(ô²)^m`. -/
def sqWord {m : ℕ} (g : Fin m → Fin 3) : List (Fin 3) :=
  (List.ofFn g).flatMap (fun a => [a, a])

/-- The square word realises the ordered product of squared axis operators:
`ô^{sqWord g} = ∏_j (ô^{(g j)})²`. -/
theorem cartWord_sqWord (A : Λ → Bool) (N : ℕ) {m : ℕ} (g : Fin m → Fin 3) :
    cartWord A N (sqWord g) = (List.ofFn fun j => stagOpVec A N (g j) ^ 2).prod := by
  have h : ∀ l : List (Fin 3),
      cartWord A N (l.flatMap (fun a => [a, a]))
        = (l.map (fun a => stagOpVec A N a ^ 2)).prod := by
    intro l
    induction l with
    | nil => simp [cartWord]
    | cons a t ih =>
      rw [List.flatMap_cons, cartWord_append, ih, List.map_cons, List.prod_cons]
      congr 1
      rw [cartWord]
      simp [pow_two]
  rw [sqWord, h, List.map_ofFn]
  rfl

/-- The square word doubles every per-letter count:
`(sqWord g).count α = 2 · (List.ofFn g).count α`. -/
theorem count_sqWord {m : ℕ} (g : Fin m → Fin 3) (α : Fin 3) :
    (sqWord g).count α = 2 * (List.ofFn g).count α := by
  have h : ∀ l : List (Fin 3),
      (l.flatMap (fun a => [a, a])).count α = 2 * l.count α := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.flatMap_cons, List.count_append, ih,
        show ([a, a] : List (Fin 3)) = [a] ++ [a] from rfl, List.count_append,
        show (a :: t) = [a] ++ t from rfl, List.count_append]
      ring
  rw [sqWord, h]

/-- The square word has length `2m`. -/
theorem length_sqWord {m : ℕ} (g : Fin m → Fin 3) : (sqWord g).length = 2 * m := by
  rw [sqWord, List.length_flatMap, List.map_ofFn, List.sum_ofFn]
  simp [mul_comm]

/-- **Squared order operator as doubled Cartesian words** (Tasaki eq. (4.2.59) main part).  The
`m`-th power of the rotationally invariant squared order operator `ô² = Σ_α (ô^{(α)})²` expands into
the sum over axis configurations `g : Fin m → Fin 3` of the square-word Cartesian order operators:
`(ô²)^m = Σ_g ô^{sqWord g}`.  Proved via the noncommutative multinomial theorem
`pow_sum_smul_eq_sum_smul_prod` at trivial scalars. -/
theorem orderSqOp_pow_eq_sum_cartWord (A : Λ → Bool) (N m : ℕ) :
    orderSqOp A N ^ m = ∑ g : Fin m → Fin 3, cartWord A N (sqWord g) := by
  rw [orderSqOp,
    show (∑ α : Fin 3, stagOpVec A N α ^ 2)
        = ∑ α : Fin 3, (1 : ℂ) • (stagOpVec A N α ^ 2) by simp,
    pow_sum_smul_eq_sum_smul_prod (fun _ => (1 : ℂ)) (fun α => stagOpVec A N α ^ 2) m]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Finset.prod_const_one, one_smul]
  exact (cartWord_sqWord A N g).symm

/-! ### The sphere monomial moment is non-negative -/

/-- The sphere monomial moment is non-negative: `0 ≤ sphereMonomialMoment k`.  Either all
exponents are even (non-negative double-factorial closed form), or the moment vanishes. -/
theorem sphereMonomialMoment_nonneg (k : Fin 3 → ℕ) : 0 ≤ sphereMonomialMoment k := by
  rw [sphereMonomialMoment]
  split_ifs with h
  · positivity
  · exact le_refl 0

/-! ### The pinch polynomial prefactor -/

/-- The **pinch polynomial prefactor** `cartPinchPoly m` of Proposition 4.10 (Tasaki §4.2.2,
p. 108): the explicit `m`-dependent constant (independent of the lattice, spin and state)
multiplying the self-contained operator-norm scale `(V·N)^{2m−2} · ⟨Φ, Φ⟩.re` in the pinch
remainder.  It bundles the total sphere-moment weight `Σ_f sphereMonomialMoment(count f)`, the
`(4π/(2m+1)) · 3^m` weight of the squared configurations and the swap-chain/branching bound
`((2m)(2m)) · (9(2m))`. -/
noncomputable def cartPinchPoly (m : ℕ) : ℝ :=
  ((∑ f : Fin (2 * m) → Fin 3, sphereMonomialMoment (fun α => (List.ofFn f).count α))
      + 4 * Real.pi / (2 * m + 1) * 3 ^ m)
    * ((2 * m) * (2 * m)) * (9 * (2 * m))

/-! ### The pinch scalar band identity -/

/-- **Proposition 4.10 pinch scalar band identity** (Tasaki §4.2.2, p. 108, eqs. (4.2.58)/(4.2.59)).
For a total-spin singlet `Φ` (annihilated by the `Ŝ³` and `Ŝ¹` generators) the real expectation of
the `2m`-th sphere average of the direction order operator equals the rotationally invariant main
part `(4π/(2m+1)) ⟨Φ, (ô²)^m Φ⟩.re` up to an `O((V·N)^{2m−2})` remainder:

`|⟨Φ, (∫_{S²} (Ô_L^n)^{2m} dσ) Φ⟩.re − (4π/(2m+1)) ⟨Φ, (ô²)^m Φ⟩.re|
    ≤ cartPinchPoly m · (V·N)^{2m−2} · ⟨Φ, Φ⟩.re`.

Both the ordered configurations `List.ofFn f` (with the sphere monomial moment weight, odd ones
vanishing) and the squared configurations `sqWord g` are contracted to their grouped normal form via
the PR-3.3a real band; the main parts coincide after the double-factorial coefficient match
`pinch_coeff_match`, and the remainder is aggregated from the self-contained operator-norm band. -/
theorem cartWord_sphereAverage_pinch (A : Λ → Bool) (hN : 1 ≤ N)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) (m : ℕ) :
    |(star Φ ⬝ᵥ (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * m)
            ∂volume.toSphere).mulVec Φ).re
        - 4 * Real.pi / (2 * m + 1)
            * (star Φ ⬝ᵥ (orderSqOp A N ^ m).mulVec Φ).re|
      ≤ cartPinchPoly m * ((Fintype.card Λ : ℝ) * N) ^ (2 * m - 2) * (star Φ ⬝ᵥ Φ).re := by
  classical
  -- Self-pairing is non-negative.
  have hΦnn : 0 ≤ (star Φ ⬝ᵥ Φ).re := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (Φ i).re, sq_nonneg (Φ i).im]
  set band : ℝ := ((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ)
      * (9 * ((2 * m : ℕ) : ℝ)
          * (((Fintype.card Λ : ℝ) * N) ^ (2 * m - 2) * (star Φ ⬝ᵥ Φ).re)) with hband
  set MT : ℝ := ∑ f : Fin (2 * m) → Fin 3,
      sphereMonomialMoment (fun α => (List.ofFn f).count α) with hMT
  -- LHS as a moment-weighted sum of ordered word expectations.
  have hop : (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * m) ∂volume.toSphere)
      = ∑ f : Fin (2 * m) → Fin 3,
          ((sphereMonomialMoment (fun α => (List.ofFn f).count α) : ℝ) : ℂ)
            • cartWord A N (List.ofFn f) := by
    rw [sphereAverage_directionStaggeredOp_pow A N (2 * m)]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [cartWord_ofFn, funext (fun α => LatticeSystem.Math.count_ofFn_eq_card_filter f α)]
  have hlhs : (star Φ ⬝ᵥ (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ (2 * m)
            ∂volume.toSphere).mulVec Φ).re
      = ∑ f : Fin (2 * m) → Fin 3,
          sphereMonomialMoment (fun α => (List.ofFn f).count α)
            * (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ).re := by
    rw [hop, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  -- RHS as a sum of square-word expectations.
  have hrhs : (star Φ ⬝ᵥ (orderSqOp A N ^ m).mulVec Φ).re
      = ∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re := by
    rw [orderSqOp_pow_eq_sum_cartWord, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  -- Per-configuration ordered → grouped band.
  have hbandL : ∀ f : Fin (2 * m) → Fin 3,
      |(star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ).re
          - (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re| ≤ band := by
    intro f
    obtain ⟨k, hk, hchain⟩ := ofFn_swapChain_groupedFin3 f
    have hlen : (List.ofFn f).length = 2 * m := List.length_ofFn
    have hb := cartWord_swapChain_re_diff_norm_le A N hN Φ h3 h1 (2 * m) hchain hlen
    rw [hband]
    refine le_trans hb (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact_mod_cast hk
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hΦnn)
  have hbandR : ∀ g : Fin m → Fin 3,
      |(star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re
          - (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => 2 * (List.ofFn g).count α))).mulVec Φ).re| ≤ band := by
    intro g
    obtain ⟨k, hk, hchain⟩ := ofFn_swapChain_groupedFin3 ((sqWord g).get)
    rw [List.ofFn_get] at hchain
    have hcnt : (fun i => (sqWord g).count i) = (fun α => 2 * (List.ofFn g).count α) :=
      funext (fun i => count_sqWord g i)
    rw [hcnt] at hchain
    have hlen : (sqWord g).length = 2 * m := length_sqWord g
    have hb := cartWord_swapChain_re_diff_norm_le A N hN Φ h3 h1 (2 * m) hchain hlen
    rw [hband]
    refine le_trans hb (mul_le_mul_of_nonneg_right ?_ ?_)
    · rw [hlen] at hk; exact_mod_cast hk
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hΦnn)
  -- Main-part equality via grouping and the coefficient match.
  have hLM : (∑ f : Fin (2 * m) → Fin 3,
        sphereMonomialMoment (fun α => (List.ofFn f).count α)
          * (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re)
      = ∑ k ∈ Finset.Nat.antidiagonalTuple 3 (2 * m),
          (Nat.multinomial Finset.univ k : ℝ)
            * (sphereMonomialMoment k
                * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 k)).mulVec Φ).re) :=
    config_sum_eq_multinomial_sum (fun k => sphereMonomialMoment k
      * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 k)).mulVec Φ).re)
  have hRM : (∑ g : Fin m → Fin 3,
        (star Φ ⬝ᵥ (cartWord A N
            (groupedFin3 (fun α => 2 * (List.ofFn g).count α))).mulVec Φ).re)
      = ∑ h ∈ Finset.Nat.antidiagonalTuple 3 m,
          (Nat.multinomial Finset.univ h : ℝ)
            * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re :=
    config_sum_eq_multinomial_sum (fun k =>
      (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * k α))).mulVec Φ).re)
  have hmain : (∑ k ∈ Finset.Nat.antidiagonalTuple 3 (2 * m),
        (Nat.multinomial Finset.univ k : ℝ)
          * (sphereMonomialMoment k
              * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 k)).mulVec Φ).re))
      = 4 * Real.pi / (2 * m + 1)
          * (∑ h ∈ Finset.Nat.antidiagonalTuple 3 m,
              (Nat.multinomial Finset.univ h : ℝ)
                * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re) := by
    set Ψ : (Fin 3 → ℕ) → ℝ := fun k =>
      (Nat.multinomial Finset.univ k : ℝ)
        * (sphereMonomialMoment k
            * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 k)).mulVec Φ).re) with hΨ
    have hDinj : Set.InjOn (fun h : Fin 3 → ℕ => fun α => 2 * h α)
        (Finset.Nat.antidiagonalTuple 3 m : Finset (Fin 3 → ℕ)) := by
      intro h₁ _ h₂ _ he
      funext α
      have hα : 2 * h₁ α = 2 * h₂ α := congrFun he α
      omega
    have hsub : (Finset.Nat.antidiagonalTuple 3 m).image
          (fun h : Fin 3 → ℕ => fun α => 2 * h α)
        ⊆ Finset.Nat.antidiagonalTuple 3 (2 * m) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨h, hh, rfl⟩ := hk
      rw [Finset.Nat.mem_antidiagonalTuple] at hh ⊢
      simp only [← Finset.mul_sum, hh]
    have hvanish : ∀ k ∈ Finset.Nat.antidiagonalTuple 3 (2 * m),
        k ∉ (Finset.Nat.antidiagonalTuple 3 m).image
              (fun h : Fin 3 → ℕ => fun α => 2 * h α) → Ψ k = 0 := by
      intro k hk hkni
      rw [Finset.Nat.mem_antidiagonalTuple] at hk
      have hodd : ¬ (∀ i, Even (k i)) := by
        intro heven
        apply hkni
        rw [Finset.mem_image]
        refine ⟨fun α => k α / 2, ?_, ?_⟩
        · have h2 : 2 * (∑ α : Fin 3, k α / 2) = 2 * m := by
            rw [Finset.mul_sum,
              Finset.sum_congr rfl fun α _ =>
                (by obtain ⟨c, hc⟩ := heven α; omega : 2 * (k α / 2) = k α)]
            exact hk
          rw [Finset.Nat.mem_antidiagonalTuple]
          show ∑ i, k i / 2 = m
          omega
        · funext α
          change 2 * (k α / 2) = k α
          obtain ⟨c, hc⟩ := heven α
          omega
      rw [hΨ]
      simp only [sphereMonomialMoment, if_neg hodd, mul_zero, zero_mul]
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_image hDinj, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [Finset.Nat.mem_antidiagonalTuple] at hh
    rw [hΨ]
    change (Nat.multinomial Finset.univ (fun α => 2 * h α) : ℝ)
          * (sphereMonomialMoment (fun α => 2 * h α)
              * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re)
        = 4 * Real.pi / (2 * m + 1)
            * ((Nat.multinomial Finset.univ h : ℝ)
                * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re)
    have hmom : sphereMonomialMoment (fun α => 2 * h α)
        = 4 * Real.pi * ((∏ i, ((2 * h i - 1)‼ : ℕ)) : ℝ) / (((2 * (∑ i, h i)) + 1)‼ : ℝ) := by
      have hev : ∀ i, Even (2 * h i) := fun i => ⟨h i, two_mul (h i)⟩
      rw [sphereMonomialMoment, if_pos hev, Finset.mul_sum Finset.univ h 2]
      push_cast
      ring
    have hγ := LatticeSystem.Math.pinch_coeff_match h
    rw [hmom]
    rw [show (Nat.multinomial Finset.univ (fun α => 2 * h α) : ℝ)
        * (4 * Real.pi * ((∏ i, ((2 * h i - 1)‼ : ℕ)) : ℝ) / (((2 * (∑ i, h i)) + 1)‼ : ℝ)
            * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re)
        = ((Nat.multinomial Finset.univ (fun i => 2 * h i) : ℝ)
              * (4 * Real.pi * ((∏ i, ((2 * h i - 1)‼ : ℕ)) : ℝ)
                  / (((2 * (∑ i, h i)) + 1)‼ : ℝ)))
            * (star Φ ⬝ᵥ (cartWord A N (groupedFin3 (fun α => 2 * h α))).mulVec Φ).re by ring]
    rw [hγ, hh]
    ring
  have hMAIN : (∑ f : Fin (2 * m) → Fin 3,
        sphereMonomialMoment (fun α => (List.ofFn f).count α)
          * (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re)
      = 4 * Real.pi / (2 * m + 1)
          * (∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => 2 * (List.ofFn g).count α))).mulVec Φ).re) := by
    rw [hLM, hmain, hRM]
  -- Remainder aggregation.
  have habsL : |(∑ f : Fin (2 * m) → Fin 3,
        sphereMonomialMoment (fun α => (List.ofFn f).count α)
          * (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ).re)
      - (∑ f : Fin (2 * m) → Fin 3,
          sphereMonomialMoment (fun α => (List.ofFn f).count α)
            * (star Φ ⬝ᵥ (cartWord A N
                (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re)|
      ≤ MT * band := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [hMT, Finset.sum_mul]
    refine Finset.sum_le_sum (fun f _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (sphereMonomialMoment_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hbandL f) (sphereMonomialMoment_nonneg _)
  have habsR : |(∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re)
      - (∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N
          (groupedFin3 (fun α => 2 * (List.ofFn g).count α))).mulVec Φ).re)|
      ≤ (3 ^ m : ℝ) * band := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun g _ => hbandR g)) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- Assemble.
  rw [hlhs, hrhs]
  have hBC : |(∑ f : Fin (2 * m) → Fin 3,
        sphereMonomialMoment (fun α => (List.ofFn f).count α)
          * (star Φ ⬝ᵥ (cartWord A N
              (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re)
      - 4 * Real.pi / (2 * m + 1)
          * (∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re)|
      ≤ 4 * Real.pi / (2 * m + 1) * ((3 ^ m : ℝ) * band) := by
    have heq : (∑ f : Fin (2 * m) → Fin 3,
          sphereMonomialMoment (fun α => (List.ofFn f).count α)
            * (star Φ ⬝ᵥ (cartWord A N
                (groupedFin3 (fun α => (List.ofFn f).count α))).mulVec Φ).re)
        - 4 * Real.pi / (2 * m + 1)
            * (∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re)
        = 4 * Real.pi / (2 * m + 1)
            * ((∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N
                (groupedFin3 (fun α => 2 * (List.ofFn g).count α))).mulVec Φ).re)
              - (∑ g : Fin m → Fin 3, (star Φ ⬝ᵥ (cartWord A N (sqWord g)).mulVec Φ).re)) := by
      rw [hMAIN]; ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_sub_comm]
    exact habsR
  refine le_trans (abs_sub_le _ _ _) (le_trans (add_le_add habsL hBC) (le_of_eq ?_))
  rw [cartPinchPoly, hband, hMT]
  push_cast
  ring

end LatticeSystem.Quantum
