import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.StaggeredOrderDoubleCommutator

/-!
# Test coverage for the §3.4 locality core, eqs. (3.4.9)-(3.4.11)

Fixtures for `LatticeSystem/Quantum/SpinS/LocalDoubleCommutatorBound.lean` (PR-2 of the §3.4
backfill arc), covering H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st
ed., Springer, 2020), §3.4, pp. 66-67: the localised inner commutator eq. (3.4.9), the localised
double commutator eq. (3.4.10), the general-window norm kernel it feeds, and the capstone eq.
(3.4.11). Design frozen in `.self-local/reports/design-pr2-eq3411.md`.

## What each block pins

**Signature pins.** `commutator_orderSum_eq_windowSum` (3.4.9),
`doubleCommutator_orderSum_eq_windowSum` (3.4.10),
`manyBodyOperatorNormS_doubleCommutator_le_of_windows` (the general norm kernel, variable
window bound `mW`) and `doubleCommutator_bondLocal_expectation_le` (3.4.11 capstone) are each pinned
as the declaration's own statement, discharged only by the identifier itself, so a pin fails
exactly when the identifier does not resolve. The two collapse identities are pinned with `W b` on
**both** the outer window index and the inner window index (not `Finset.univ`), so a vacuous
`W b = univ` instantiation would not satisfy the pin. The kernel pin fixes the exact constant
`4 * (mW : ℝ) ^ 2 * h₀ * o₀ ^ 2 * (B.card : ℝ)` with `mW` left as a *variable*, per the design's
generality obligation (§6-7): a hard-coded `mW = 2` bond-only statement would not distinguish the
correct counting from the four wrong constants the design records. The capstone pin fixes both
conjuncts, the literal `16`, the `(L : ℝ) ^ d` factor, and the exact hypothesis list — in
particular that **no** (3.4.3)/(3.4.4)/Hermiticity hypothesis appears anywhere among the eight
named hypotheses (`hW`, `hoo`, `hnh`, `hno`, `hh₀`, `ho₀`, `hbond`, `hB`) plus the normalization
`hΦ`.

**Numeric fixtures.** The kernel constant-correctness guard from the design (§7): at
`mW := 3`, `h₀ := 5/2`, `o₀ := 1/2`, `B.card := 7` the correct constant evaluates to `315/2`. The
design records five plausible mis-countings that each give a *different* wrong value at this point
(`52.5`, `78.75`, `315`, `472.5`, `787.5`), so a `≤ 315/2` fixture built from a bound *tighter* than
`315/2` (`≤` in the same direction as every one of the five, since all five exceed `315/2` except
one — see the per-value note below) would not be reachable from any of them; the fixture is stated
as an `≤` inequality on `manyBodyOperatorNormS`, matching the kernel's own conclusion shape, rather
than as an equality, since the kernel produces a bound not an identity. `mW = 3 ≠ 2` is deliberate:
at the bond point `mW = 2`, `4 mW²`, `8 mW`, `2 mW³` and `mW⁴` all coincide with `16`, so a fixture
at `mW = 2` could not separate the correct exponent/factor pattern from any of them. The capstone
fixture instantiates at `d := 3`, `L := 4`, `h₀ := 5/2`, `o₀ := 1/2`, giving the literal `1920`
(`16 · 3 · (5/2) · (1/4) · 64`); `d ≠ L` and `L^d = 64 ≠ d^L = 81` pin the `d · L^d` shape against a
`d^L` slip, and a `32` or `8` leading constant would give `3840` or `960` respectively.

## Off-by-two window-index guard (design §7, closing remark)

The design records that the collapse in (3.4.10) uses `|W b| ≤ mW` for **both** the innermost
(`z`) sum and the middle (`x`) sum of the norm kernel's triple sum — i.e. it is genuinely a single
window applied on both index positions, not two independently-bounded windows `W`/`W₂` that happen
to coincide. Per the frozen decision (design §0 item 2, §3.B "why one window and not two"), the
statement itself carries only one window parameter `W` and one bound `mW`; there is no `W₂`/`mW₂`
pair to instantiate unequally, so **the swap the coordinator originally flagged cannot be expressed
by any instantiation of this signature** — a fixture that tried to make `|W b| ≤ mW` apply to `x`
and a *different* `mW₂` apply to `z` would not type-check against
`manyBodyOperatorNormS_doubleCommutator_le_of_windows`'s actual hypothesis list (`hcard : ∀ b ∈ B,
(W b).card ≤ mW`, one bound, no second bound). This is recorded here explicitly, per the
orchestrator's instruction, rather than manufactured as a fixture that could not fail: the
single-window numeric guard above (`mW := 3` distinguishing `4mW²` from `8mW`/`2mW³`/`mW⁴`) is the
residual check the frozen design leaves available, and it *is* exercised as fixture 1.

## Duplicate assessment

`manyBodyOperatorNormS_comm_le` (`ManyBodyOperatorNorm.lean`, relocated from
`LiebSchultzMattisTaylorBound.lean` by this same PR) and `expectation_abs_le_manyBodyOperatorNormS`
(`ExpectationNormBound.lean`) are both consumed by, but not restated by, the capstone pin: the
first conjunct of `doubleCommutator_bondLocal_expectation_le` is exactly
`expectation_abs_le_manyBodyOperatorNormS` composed with `le_abs_self`, per the design (§3.D), so it
is not re-pinned here as an independent fact — only the capstone's own two-conjunct signature is
pinned, once, above.

## Re-derivation pin

`staggeredOrderOpS_double_commutator` (`StaggeredOrderDoubleCommutator.lean`) is expected to keep
its statement unchanged after being re-derived (design §5) from the new `Math/CommutatorSum.lean`
primitives. This is pinned as a signature pin against its **current** (pre-re-derivation) statement,
so that after the re-derivation lands, this same pin continues to typecheck only if the statement
was not altered; a change to the statement would make this pin fail to elaborate against the new
declaration, which is the intended regression signal.
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

/-- **Signature pin (re-derivation).** `staggeredOrderOpS_double_commutator` must keep this exact
statement after being re-derived (design §5) from the `Math/CommutatorSum.lean` primitives instead
of an inline distribution argument. -/
example (A : Λ → Bool) (H : ManyBodyOpS Λ N) :
    staggeredOrderOpS A N * (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H)
        - (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H) * staggeredOrderOpS A N
      = ∑ x : Λ, ∑ z : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A z then (1 : ℂ) else -1))
            • (spinSSiteOp3 x N * (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H)
                - (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H) * spinSSiteOp3 x N) :=
  staggeredOrderOpS_double_commutator A N H

/-! ## Numeric fixture 1: the kernel constant-correctness guard (design §7 item 3) -/

/-- **Fixture (kernel constant guard).** At `mW := 3`, `h₀ := 5/2`, `o₀ := 1/2`, `B.card := 7` the
kernel's constant evaluates to `315/2`. Every one of the design's five plausible mis-countings
gives a numerically distinct value at this point (`52.5`, `78.75`, `315`, `472.5`, `787.5`), so this
is a genuine discrimination point and not merely a plausibility check. Stated over *abstract*
`B, hb, o, W` constrained only by the kernel's own hypotheses, so `norm_num` cannot close the goal
without invoking the theorem. -/
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

/-! ## Numeric fixture 2: the capstone constant (design §7 item 4) -/

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
