import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.StaggeredOrderDoubleCommutator

/-!
# Test coverage for the §3.4 locality core, eqs. (3.4.9)-(3.4.11)

Fixtures for `LatticeSystem/Quantum/SpinS/LocalDoubleCommutatorBound.lean`, covering H. Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §3.4, pp. 66-67:
the localised inner commutator eq. (3.4.9), the localised double commutator eq. (3.4.10), the
general-window norm kernel they feed, and the capstone eq. (3.4.11).

## What each block pins

**Signature pins.** `commutator_orderSum_eq_windowSum` (3.4.9),
`doubleCommutator_orderSum_eq_windowSum` (3.4.10),
`manyBodyOperatorNormS_doubleCommutator_le_of_windows` (the general norm kernel, variable
window bound `mW`) and `doubleCommutator_bondLocal_expectation_le` (3.4.11 capstone) are each pinned
as the declaration's own statement, discharged only by the identifier itself, so a pin fails
exactly when the identifier does not resolve. The two collapse identities are pinned with `W b` on
**both** the outer window index and the inner window index (not `Finset.univ`), so a vacuous
`W b = univ` instantiation would not satisfy the pin. The kernel pin fixes the exact constant
`4 * (mW : ℝ) ^ 2 * h₀ * o₀ ^ 2 * (B.card : ℝ)` with `mW` left as a *variable*: at the bond point
`mW = 2` the candidate constants `4 mW²`, `8 mW`, `2 mW³` and `mW⁴` all coincide with `16`, so a
hard-coded `mW = 2` statement could not separate them. The capstone pin fixes both conjuncts, the
literal `16`, the `(L : ℝ) ^ d` factor, and the exact hypothesis list — in particular that **no**
(3.4.3)/(3.4.4)/Hermiticity hypothesis appears anywhere among the eight named hypotheses (`hW`,
`hoo`, `hnh`, `hno`, `hh₀`, `ho₀`, `hbond`, `hB`) plus the normalization `hΦ`.

**Numeric fixtures.** The kernel fixture instantiates at `mW := 3`, `h₀ := 5/2`, `o₀ := 1/2`,
`B.card := 7`, where the correct constant evaluates to `315/2` and the three competing patterns take
the pairwise distinct values `105` (`8 mW`), `945/4` (`2 mW³`) and `2835/8` (`mW⁴`). The
discriminating step is the intermediate `have`, whose constant is spelled out as
`4 * (3 : ℝ) ^ 2 * (5 / 2) * (1 / 2) ^ 2 * (B.card : ℝ)` and which is closed by the kernel itself:
a kernel with a different exponent/factor pattern yields a syntactically different constant and
does not close that `have`. The final `≤ 315/2` goal is strictly weaker — `8 mW` would give
`105 ≤ 315/2` and still satisfy it — so the numeric endpoint alone rules out only the patterns
whose value at this point exceeds `315/2`. The fixture is stated as an `≤` inequality on
`manyBodyOperatorNormS`, matching the kernel's own conclusion shape, since the kernel produces a
bound and not an identity. The capstone fixture instantiates at `d := 3`, `L := 4`, `h₀ := 5/2`,
`o₀ := 1/2`, giving the literal `1920` (`16 · 3 · (5/2) · (1/4) · 64`); `d ≠ L` and
`L^d = 64 ≠ d^L = 81` pin the `d · L^d` shape against a `d^L` slip, and a `32` or `8` leading
constant would give `3840` or `960` respectively.

## Two windows, and the one-window instance

The collapse of the triple sum uses an inner window `W₁ b` on the innermost (`z`) sum and an outer
window `W₂ b` on the middle (`x`) sum, bounded independently by `m₁` and `m₂`, with the kernel
constant `4 m₁ m₂ h₀ o₀² |B|`. The one-window statements pinned above are the instance
`W₁ = W₂`, `m₁ = m₂ = mW`, where `4 m₁ m₂` collapses to `4 mW²`; they are *derived* from the
two-window core, so no argument is proved twice. Since `4 m₁ m₂` is symmetric in `m₁` and `m₂`, no
numeric fixture can separate a swap of the two window bounds; what pins the roles is the hypothesis
shape — `hW` constrains the inner window and the `x ∉ W₂ b` binder the outer one — together with
the range-`r` capstone of `Tests/RangeLocalDoubleCommutatorBound.lean`, where the inner window is
the `2r`-ball, bounded by `(4r+1)^d`, and the outer window is the `4r`-ball, bounded by
`(8r+1)^d`, so the two window bounds are not interchangeable.

## Duplicate assessment

`manyBodyOperatorNormS_comm_le` (`ManyBodyOperatorNorm.lean`) and
`expectation_abs_le_manyBodyOperatorNormS` (`ExpectationNormBound.lean`) are both consumed by, but
not restated by, the capstone pin: the first conjunct of `doubleCommutator_bondLocal_expectation_le`
is exactly `expectation_abs_le_manyBodyOperatorNormS` composed with `le_abs_self`, so it is not
re-pinned here as an independent fact — only the capstone's own two-conjunct signature is pinned,
once, above.

## Re-derivation pin

`staggeredOrderOpS_double_commutator` (`StaggeredOrderDoubleCommutator.lean`) is derived from the
`Math/CommutatorSum.lean` primitives. Its full statement is pinned here as a signature pin, so any
alteration of that statement makes the pin fail to elaborate.
-/

namespace LatticeSystem.Tests.LocalDoubleCommutatorBound

open LatticeSystem
open LatticeSystem.Quantum
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pins -/

/-- **Signature pin (eq. (3.4.9)).** The localised inner commutator: `[Ĥ, Ô] = Σ_{b∈B} Σ_{z∈W b}
[ĥ_b, ô_z]`, given that `ĥ_b` commutes with every `ô_z` for `z` outside its window `W b`. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z)) :
    (∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)
      = ∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b) :=
  commutator_orderSum_eq_windowSum B hb o W hW

/-- **Signature pin (eq. (3.4.10)).** The localised double commutator: `[Ô, [Ĥ, Ô]] = Σ_{b∈B}
Σ_{x∈W b} Σ_{z∈W b} [ô_x, [ĥ_b, ô_z]]`, given the same window-commutation hypothesis as (3.4.9)
plus site-disjoint commutation of the `ô_x` among themselves. Both the outer (`x`) and inner (`z`)
sums collapse onto the **same** window `W b`, not `Finset.univ`. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z)) :
    (∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
        - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)) * (∑ x : Λ, o x)
      = ∑ b ∈ B, ∑ x ∈ W b, ∑ z ∈ W b,
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x) :=
  doubleCommutator_orderSum_eq_windowSum B hb o W hW hoo

/-- **Signature pin (norm kernel).** `‖[Ô, [Ĥ, Ô]]‖ ≤ 4 mW² h₀ o₀² |B|` for a *variable* window
bound `mW`, given per-bond and per-site norm bounds `h₀`, `o₀`, nonnegativity of `o₀`, and a
window-cardinality bound `mW`. This is the general-window kernel from which the (3.4.11) capstone
is obtained by specialising `mW := 2`. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) (h₀ o₀ : ℝ) (mW : ℕ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀) (ho₀ : 0 ≤ o₀)
    (hcard : ∀ b ∈ B, (W b).card ≤ mW) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (mW : ℝ) ^ 2 * h₀ * o₀ ^ 2 * (B.card : ℝ) :=
  manyBodyOperatorNormS_doubleCommutator_le_of_windows B hb o W h₀ o₀ mW hW hoo hnh hno ho₀ hcard

/-- **Signature pin (eq. (3.4.11) capstone).** The two-step bound
`⟨Φ_GS|[Ô,[Ĥ,Ô]]|Φ_GS⟩.re ≤ ‖[Ô,[Ĥ,Ô]]‖ ≤ 16 d h₀ o₀² L^d` for a normalized `Φ`, bond-local windows
(`|W b| ≤ 2`), and a bond-count bound `|B| ≤ d L^d`. No (3.4.3)/(3.4.4)/Hermiticity hypothesis
appears among the eight hypotheses, and no `1 ≤ L`/`1 ≤ d` hypothesis is present either. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) (d L : ℕ) (h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (d : ℝ) * (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x)) Φ
      ≤ manyBodyOperatorNormS
          ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
              * (∑ x : Λ, o x))
      ∧ manyBodyOperatorNormS
          ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
              * (∑ x : Λ, o x))
        ≤ 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d :=
  doubleCommutator_bondLocal_expectation_le B hb o W d L h₀ o₀ hW hoo hnh hno hh₀ ho₀ hbond hB hΦ

/-! ## Re-derivation pin -/

/-- **Signature pin (re-derivation).** `staggeredOrderOpS_double_commutator`, derived from the
`Math/CommutatorSum.lean` primitives, has exactly this statement. -/
example (A : Λ → Bool) (H : ManyBodyOpS Λ N) :
    staggeredOrderOpS A N * (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H)
        - (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H) * staggeredOrderOpS A N
      = ∑ x : Λ, ∑ z : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A z then (1 : ℂ) else -1))
            • (spinSSiteOp3 x N * (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H)
                - (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H) * spinSSiteOp3 x N) :=
  staggeredOrderOpS_double_commutator A N H

/-! ## Numeric fixture 1: the kernel constant-correctness guard -/

/-- **Fixture (kernel constant guard).** At `mW := 3`, `h₀ := 5/2`, `o₀ := 1/2`, `B.card := 7` the
kernel's constant evaluates to `315/2`, while `8 mW`, `2 mW³` and `mW⁴` give the distinct values
`105`, `945/4` and `2835/8`. The discrimination is carried by the intermediate `have`, which spells
the constant out as `4 * (3 : ℝ) ^ 2 * (5 / 2) * (1 / 2) ^ 2 * (B.card : ℝ)` and is closed by the
kernel itself, so a kernel with a different exponent/factor pattern does not close it. Stated over
*abstract* `B, hb, o, W` constrained only by the kernel's own hypotheses, so `norm_num` cannot close
the goal without invoking the theorem. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ (5 / 2 : ℝ))
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ (1 / 2 : ℝ))
    (hcard : ∀ b ∈ B, (W b).card ≤ 3) (hcardB : B.card = 7) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ (315 / 2 : ℝ) := by
  have h : manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (3 : ℝ) ^ 2 * (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ 2 * (B.card : ℝ) :=
    manyBodyOperatorNormS_doubleCommutator_le_of_windows B hb o W (5 / 2) (1 / 2) 3
      hW hoo hnh hno (by norm_num) hcard
  rw [hcardB] at h
  norm_num at h
  exact h

/-! ## Numeric fixture 2: the capstone constant -/

/-- **Fixture (capstone constant guard).** At `d := 3`, `L := 4`, `h₀ := 5/2`, `o₀ := 1/2` the
capstone's upper bound `16 d h₀ o₀² L^d` evaluates to `1920`, obtained by applying the capstone
theorem itself (not by an arithmetic tautology disconnected from it). Since `L^d = 64 ≠ d^L = 81`,
this also separates the correct `d · L^d` shape from a `d^L` slip; a `32` or `8` leading constant
would give `3840` or `960` respectively. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ (5 / 2 : ℝ))
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ (1 / 2 : ℝ))
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (3 : ℝ) * (4 : ℝ) ^ (3 : ℕ))
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ (1920 : ℝ) := by
  have h : manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 16 * (3 : ℝ) * (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ 2 * (4 : ℝ) ^ (3 : ℕ) :=
    (doubleCommutator_bondLocal_expectation_le B hb o W 3 4 (5 / 2) (1 / 2)
      hW hoo hnh hno (by norm_num) (by norm_num) hbond hB hΦ).2
  norm_num at h
  exact h

end LatticeSystem.Tests.LocalDoubleCommutatorBound
