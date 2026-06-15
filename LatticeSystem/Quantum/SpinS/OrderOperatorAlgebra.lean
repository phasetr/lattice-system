import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tasaki §4.2.2: the order-operator algebra and Lemma 4.14

The proofs of the tower theorems use the per-volume order operators `ô^± = Ô_L^± / V` (`V = L^d`)
and
the `U(1)`-symmetric order operator `p̂ = ½(ô^+ ô^- + ô^- ô^+)` (eqs. (4.2.30)–(4.2.31)).  The
commutator `[Ô_L^+, Ô_L^-] = 2 Ŝ_tot^{(3)}` (eq. (4.2.32)) gives `‖[ô^+, ô^-]‖ ≤ o₀/V` with `o₀ =
2S`
(eq. (4.2.33)), whence the key elementary bound:

**Lemma 4.14** (eq. (4.2.34)): for any balanced sign sequence `s₁, …, s_{2n} ∈ {+, −}` (`n` pluses
and `n` minuses), the operator norm of the difference between the product and `p̂ⁿ` is small,
`‖ô^{s₁} ⋯ ô^{s_{2n}} − p̂ⁿ‖ ≤ n² (o₀)^{2n−1} / V`,
because any balanced product can be rearranged to any other by at most `n²` neighboring `±`
exchanges,
each costing `≤ ‖[ô^+, ô^-]‖ ≤ o₀/V`.

This file defines the order-operator algebra and records Lemma 4.14 as a documented axiom (the
operator-norm / commutator-rearrangement proof is elementary but involved; a finite-volume discharge
candidate).  The operator norm is the genuine `L²` operator norm `manyBodyOperatorNormS`, *not* the
default entrywise matrix norm.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Lemma 4.14, eqs. (4.2.30)–(4.2.34), pp. 104–105 (`S = N/2`, so `o₀ = 2S = N`).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **`L²` operator (spectral) norm** of a many-body operator, via the associated continuous
linear map on `EuclideanSpace ℂ (Λ → Fin (N+1))`.  This is submultiplicative and satisfies the
triangle inequality — unlike the default entrywise matrix norm — so it is the correct norm for the
order-operator bounds. -/
noncomputable def manyBodyOperatorNormS (M : ManyBodyOpS Λ N) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- A sign sequence `s : Fin (2n) → Bool` (`true = +`, `false = −`) is **balanced** when it has
exactly `n` pluses (hence `n` minuses), i.e. `Σ s_j = 0` in `±1` terms. -/
def BalancedSigns {n : ℕ} (s : Fin (2 * n) → Bool) : Prop :=
  (Finset.univ.filter (fun i : Fin (2 * n) => s i = true)).card = n

/-- The **per-volume order operator** `ô^{±} = Ô_L^{±} / V` (`V = L^d`, eq. (4.2.30)): the staggered
raising (`b = true`) or lowering (`b = false`) order operator, divided by the volume. -/
noncomputable def staggeredOrderDensityOpS (d L N : ℕ) [NeZero L] (b : Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  ((L : ℂ) ^ d)⁻¹ •
    (if b then staggeredRaisingOpS (torusParitySublattice d L) N
      else staggeredLoweringOpS (torusParitySublattice d L) N)

/-- The **ordered product** `ô^{s₁} ⋯ ô^{s_{2n}}` of `2n` per-volume order operators along a sign
sequence `s`. -/
noncomputable def balancedOrderProductS (d L N n : ℕ) [NeZero L] (s : Fin (2 * n) → Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  (List.ofFn fun i : Fin (2 * n) => staggeredOrderDensityOpS d L N (s i)).prod

/-- The **`U(1)`-symmetric order operator** `p̂ = ½(ô^+ ô^- + ô^- ô^+) = (ô^{(1)})² + (ô^{(2)})²`
(eq. (4.2.31)). -/
noncomputable def staggeredPhatS (d L N : ℕ) [NeZero L] : ManyBodyOpS (HypercubicTorus d L) N :=
  (2 : ℂ)⁻¹ • (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false +
    staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)

/-- **Tasaki Lemma 4.14 (order-operator algebra estimate), AXIOM.**  For any balanced sign sequence
`s` of length `2n` (`n > 0`), the `L²` operator norm of the difference between the ordered product
`ô^{s₁} ⋯ ô^{s_{2n}}` and `p̂ⁿ` is bounded by `n² (o₀)^{2n−1} / V`, where `o₀ = 2S = N` and
`V = L^d` (eq. (4.2.34)):
`‖ô^{s₁} ⋯ ô^{s_{2n}} − p̂ⁿ‖ ≤ n² N^{2n−1} / L^d`.

Any balanced product rearranges to any other by `≤ n²` neighboring `±` exchanges, each costing
`≤ ‖[ô^+, ô^-]‖ ≤ o₀/V` (eq. (4.2.33)); the bound follows with `‖ô^{±}‖ ≤ o₀`.  An elementary but
involved finite-volume estimate — recorded as a documented axiom (discharge candidate). -/
axiom staggered_balanced_order_product_norm_le {d L N n : ℕ} [NeZero L] (hn : 0 < n)
    (s : Fin (2 * n) → Bool) (hbal : BalancedSigns s) :
    manyBodyOperatorNormS (balancedOrderProductS d L N n s - staggeredPhatS d L N ^ n) ≤
      (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d

open Filter in
/-- **Tasaki Lemma 4.15 (the order parameter as a `p̂`-ratio double limit), AXIOM.**  The
symmetry-breaking order parameter `m∗` is the iterated limit of the ground-state `p̂`-ratios
(eq. (4.2.38)): `m∗ = lim_{n↑∞} liminf_{L↑∞} ⟨p̂^{n+1}⟩ / ⟨p̂^n⟩` (the `n`-ratio is increasing and
bounded, so the outer limit exists; the inner is a `liminf` per footnote 31).  We state the sound
`liminf`-lower direction — for every `ε > 0`, for all large `n`, eventually in (even) `L` the ratio
exceeds `m∗ − ε` — which captures `lim_n liminf_L ⟨p̂^{n+1}⟩/⟨p̂^n⟩ ≥ m∗`.  The axiom also records
the
`U(1)`-optimal bound `√(2 q₀) ≤ m∗` (eq. (4.2.39), the weaker `√2` companion of Theorem 4.11's
`√3`).

`m∗` is the genuine order parameter, pinned (as in Theorems 4.11/4.13) by a realizing ground-state
family `Φ` with exact LRO limit `q₀`, staggered-moment limit `m∗`, `IsTanakaFullSSBConstants`, and
the
realizing slow tower `M` — unsatisfiable in `d = 1` (no LRO, Corollary 4.3), so vacuous there.  The
`p̂`-moment denominators are positive (`hPhat`, `⟨p̂^n⟩ ≥ (2q₀)^n > 0` under LRO, eq. (4.2.37)),
so the
Rayleigh-ratio division is meaningful. -/
axiom mStar_eq_phat_ratio_limit (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M)
    (hPhat : ∀ (n L : ℕ) [NeZero L], 2 ≤ L → Even L →
      0 < expectationRatioRe (staggeredPhatS d L N ^ n) (Φ L)) :
    (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        mStar - ε <
          expectationRatioRe (staggeredPhatS d L N ^ (n + 1)) (Φ L) /
            expectationRatioRe (staggeredPhatS d L N ^ n) (Φ L)) ∧
    Real.sqrt (2 * q₀) ≤ mStar

end LatticeSystem.Quantum
