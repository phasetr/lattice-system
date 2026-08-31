import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.RangeLocalDoubleCommutatorBound
import LatticeSystem.Math.Combinatorics.CoordinateBall

/-!
# Test coverage for the general range-`r` bound, Problem 3.4.a, eq. (3.4.13)

Fixtures for `LatticeSystem/Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean` and
`LatticeSystem/Math/Combinatorics/CoordinateBall.lean`, covering H. Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §3.4, Problem 3.4.a,
statement pp. 67-68, printed solution p. 501: the coordinate sup-norm ball, the two-window
generalisation of the (3.4.10) collapse and its norm kernel, and the eq. (3.4.13) capstone.

## What each block pins

**Signature pins.** `coordSupBall`, `mem_coordSupBall` and `card_coordSupBall_le`
(`Math/Combinatorics/CoordinateBall.lean`); `doubleCommutator_orderSum_eq_twoWindowSum` and
`manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows`
(`Quantum/SpinS/LocalDoubleCommutatorBound.lean`); and
`tasaki_problem_3_4_a_doubleCommutator_expectation_le`
(`Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean`) are each pinned as the declaration's own
statement, discharged only by the identifier itself. The two-window collapse and kernel pins use
**syntactically distinct** `W₁ W₂` and `m₁ m₂` binders, so a statement that secretly identified the
two windows or the two bounds would not satisfy the pin.

**Numeric fixtures.**
- F-2 (ball-count tightness, `r = 1`, `d = 2`): on `Λ := Fin 2 → Fin 3` with coordinates
  `pos y i := ((y i : ℕ) : ℤ)` and centre `c := fun _ => (1 : Fin 3)`, every site lies in the
  radius-`1` ball, so `coordSupBall pos 1 c = Finset.univ` and its card is
  `9 = (2·1+1)^2`, i.e. the bound `card_coordSupBall_le` gives is *attained*. A one-sided endpoint
  alone cannot rule out an over-large closed form; this fixture does, because it forces equality.
- F-3 (two-window kernel constant, `m₁ ≠ m₂`): abstract `B, hb, o, W₁, W₂` at `m₁ := 3`, `m₂ := 5`,
  `h₀ := 5/2`, `o₀ := 1/2`, `B.card := 7`, giving the correct constant `525/2`, discriminated from
  the competing patterns `4m₁² = 315/2`, `4m₂² = 875/2`, `8m₁m₂ = 525`, `2m₁m₂ = 525/4`
  (values re-derived below; see the fixture's own doc comment for the exact numbers).
- F-4 (capstone constant, `r = 1`, `d = 3`, `L = 2`, `h₀ = 5/2`, `o₀ = 1/2`): the correct bound is
  `67500`, discriminated from the book-solution misprint form `(2r+1)²(4r+1)^d` (`22500`) and from
  `L^d = 8 ≠ d^L = 9`.

## Coverage limits (stated honestly, following PR-2's precedent)

The kernel and capstone fixtures discriminate the constant only while the library statement and
the fixture's intermediate `have` are not both changed to the *same* wrong constant at once; a
future regression could still slip past if it altered both in lock-step. The one-sided `≤`
fixtures (F-3, F-4) cannot reject an *under-large* competing constant on their own — only F-2, which
forces an equality via `Finset.card_univ`, does that. The `m₁ ↔ m₂` swap is undetectable by any
numeric fixture on the *constant* alone, since `4 m₁ m₂` is symmetric in `m₁` and `m₂`: what pins
the window roles is the hypothesis shape (`hW`/`hWW` constrain `W₁`/`W₂` asymmetrically, and at the
capstone the outer window is forced to be the `2r`-ball because `card (coordSupBall pos (2*r) x) ≤
(2r+1)^d` is not a provable obligation).
-/

namespace LatticeSystem.Tests.RangeLocalDoubleCommutatorBound

open LatticeSystem
open LatticeSystem.Quantum
open LatticeSystem.Math
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pins: `Math/Combinatorics/CoordinateBall.lean` -/

/-- **Signature pin (`coordSupBall`).** The coordinate sup-norm ball
`B_r(x) = {y : ∀ i, |pos y i - pos x i| ≤ r}` as a `Finset Λ`, for `pos : Λ → (Fin d → ℤ)`. -/
example {d : ℕ} (pos : Λ → (Fin d → ℤ)) (r : ℕ) (x : Λ) :
    coordSupBall pos r x = Finset.univ.filter fun y => ∀ i, |pos y i - pos x i| ≤ (r : ℤ) := by
  rfl

/-- **Signature pin (`mem_coordSupBall`).** Membership in the coordinate sup-norm ball unfolds to
the coordinate-wise sup-norm bound. -/
example {d : ℕ} {pos : Λ → (Fin d → ℤ)} {r : ℕ} {x y : Λ} :
    y ∈ coordSupBall pos r x ↔ ∀ i, |pos y i - pos x i| ≤ (r : ℤ) :=
  mem_coordSupBall

/-- **Signature pin (`card_coordSupBall_le`).** `|B_r(x)| ≤ (2r+1)^d` for injective coordinates
`pos`, no `1 ≤ d` and no `0 < r` hypothesis. -/
example {d : ℕ} (pos : Λ → (Fin d → ℤ)) (hpos : Function.Injective pos) (r : ℕ) (x : Λ) :
    (coordSupBall pos r x).card ≤ (2 * r + 1) ^ d :=
  card_coordSupBall_le pos hpos r x

/-! ## Signature pins: the two-window core (`LocalDoubleCommutatorBound.lean`) -/

/-- **Signature pin (two-window collapse).** The double commutator collapses onto an *inner*
window `W₁ b` and an *outer* window `W₂ b`, syntactically distinct binders so a statement that
secretly identified them would not satisfy this pin. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W₁ W₂ : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W₁ b, Commute (hb b) (o z))
    (hWW : ∀ b ∈ B, ∀ x ∉ W₂ b, ∀ z ∈ W₁ b, Commute (o x) (hb b * o z - o z * hb b)) :
    (∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
        - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)) * (∑ x : Λ, o x)
      = ∑ b ∈ B, ∑ x ∈ W₂ b, ∑ z ∈ W₁ b,
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x) :=
  doubleCommutator_orderSum_eq_twoWindowSum B hb o W₁ W₂ hW hWW

/-- **Signature pin (two-window kernel).** `‖[Ô,[Ĥ,Ô]]‖ ≤ 4 m₁ m₂ h₀ o₀² |B|` with independent
window bounds `m₁` (inner) and `m₂` (outer), syntactically distinct so a fixture with `m₁ ≠ m₂`
genuinely exercises both binders. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W₁ W₂ : ι → Finset Λ) (h₀ o₀ : ℝ) (m₁ m₂ : ℕ)
    (hW : ∀ b ∈ B, ∀ z ∉ W₁ b, Commute (hb b) (o z))
    (hWW : ∀ b ∈ B, ∀ x ∉ W₂ b, ∀ z ∈ W₁ b, Commute (o x) (hb b * o z - o z * hb b))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀) (ho₀ : 0 ≤ o₀)
    (hcard₁ : ∀ b ∈ B, (W₁ b).card ≤ m₁) (hcard₂ : ∀ b ∈ B, (W₂ b).card ≤ m₂) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (m₁ : ℝ) * (m₂ : ℝ) * h₀ * o₀ ^ 2 * (B.card : ℝ) :=
  manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows B hb o W₁ W₂ h₀ o₀ m₁ m₂
    hW hWW hnh hno ho₀ hcard₁ hcard₂

/-! ## Signature pin: the eq. (3.4.13) capstone -/

/-- **Signature pin (eq. (3.4.13) capstone).** `⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ ≤
4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` for a normalized `Φ`, injective coordinates, range-`r`/`2r` support
conditions, and `|Λ| ≤ L^d`. No `1 ≤ d`, no `1 ≤ L`, no (3.4.3)/(3.4.4)/Hermiticity hypothesis
appears among the named hypotheses. -/
example {d : ℕ} (pos : Λ → (Fin d → ℤ)) (hpos : Function.Injective pos)
    (h o : Λ → ManyBodyOpS Λ N) (r L : ℕ) (h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hHloc : ∀ x z : Λ, z ∉ coordSupBall pos r x → Commute (h x) (o z))
    (hOloc : ∀ x z : Λ, z ∉ coordSupBall pos (2 * r) x →
      ∀ y ∈ coordSupBall pos r x, Commute (o z) (h x * o y - o y * h x))
    (hnh : ∀ x : Λ, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hΛ : (Fintype.card Λ : ℝ) ≤ (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
          - ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
            * (∑ x : Λ, o x)) Φ
      ≤ 4 * (2 * (r : ℝ) + 1) ^ d * (4 * (r : ℝ) + 1) ^ d * h₀ * o₀ ^ 2 * (L : ℝ) ^ d :=
  tasaki_problem_3_4_a_doubleCommutator_expectation_le pos hpos h o r L h₀ o₀
    hHloc hOloc hnh hno hh₀ ho₀ hΛ hΦ

/-! ## Numeric fixture F-2: ball-count tightness (`r ≥ 1`, `d ≥ 2`) -/

/-- **Fixture (ball-count tightness).** On `Λ := Fin 2 → Fin 3` with `pos y i := ((y i : ℕ) : ℤ)`
(injective) and centre `c := fun _ => (1 : Fin 3)`, every coordinate `y i ∈ {0,1,2}` satisfies
`|y i - 1| ≤ 1`, so the radius-`1` ball is *all* of `Λ`: `coordSupBall pos 1 c = Finset.univ`, of
card `Fintype.card (Fin 2 → Fin 3) = 3^2 = 9 = (2·1+1)^2`. The card is computed by
`le_antisymm` *through* `card_coordSupBall_le`, so a wrongly-large closed form breaks the fixture:
with a bound `> 9` the upper branch could not be discharged against the value `9` that the lower
branch forces. A one-sided numeric endpoint alone could not do this. -/
example :
    (coordSupBall (Λ := Fin 2 → Fin 3) (fun y i => ((y i : ℕ) : ℤ)) 1
        (fun _ => (1 : Fin 3))).card = 9 := by
  have hpos : Function.Injective (fun y : Fin 2 → Fin 3 => fun i => ((y i : ℕ) : ℤ)) := by
    intro y y' hyy'
    funext i
    have hi := congrFun hyy' i
    simp only at hi
    exact Fin.val_injective (by exact_mod_cast hi)
  have hall : coordSupBall (Λ := Fin 2 → Fin 3) (fun y i => ((y i : ℕ) : ℤ)) 1
      (fun _ => (1 : Fin 3)) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun y => mem_coordSupBall.mpr fun i => ?_
    have hlt : (y i).val < 3 := (y i).isLt
    have h1 : ((fun _ : Fin 2 => (1 : Fin 3)) i).val = 1 := rfl
    rw [abs_le]
    omega
  refine le_antisymm (le_trans (card_coordSupBall_le (Λ := Fin 2 → Fin 3)
    (fun y i => ((y i : ℕ) : ℤ)) hpos 1 (fun _ => (1 : Fin 3))) (by norm_num)) ?_
  rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  norm_num

/-! ## Numeric fixture F-3: two-window kernel constant (`m₁ ≠ m₂`) -/

/-- **Fixture (two-window kernel constant, `m₁ ≠ m₂`).** At `m₁ := 3`, `m₂ := 5`, `h₀ := 5/2`,
`o₀ := 1/2`, `B.card := 7` the kernel's constant evaluates to `4·3·5·(5/2)·(1/2)²·7 = 525/2`. The
competing patterns take the pairwise distinct values `4m₁² = 315/2`, `4m₂² = 875/2`, `8m₁m₂ = 525`,
`2m₁m₂ = 525/4`. Stated over abstract `B, hb, o, W₁, W₂` constrained only by the kernel's own
hypotheses, discriminated by an intermediate `have` closed by the kernel itself, so `norm_num`
cannot close the goal without invoking the theorem. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W₁ W₂ : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W₁ b, Commute (hb b) (o z))
    (hWW : ∀ b ∈ B, ∀ x ∉ W₂ b, ∀ z ∈ W₁ b, Commute (o x) (hb b * o z - o z * hb b))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ (5 / 2 : ℝ))
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ (1 / 2 : ℝ))
    (hcard₁ : ∀ b ∈ B, (W₁ b).card ≤ 3) (hcard₂ : ∀ b ∈ B, (W₂ b).card ≤ 5)
    (hcardB : B.card = 7) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ (525 / 2 : ℝ) := by
  have h : manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (3 : ℝ) * (5 : ℝ) * (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ 2 * (B.card : ℝ) :=
    manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows B hb o W₁ W₂ (5 / 2) (1 / 2) 3 5
      hW hWW hnh hno (by norm_num) hcard₁ hcard₂
  rw [hcardB] at h
  norm_num at h
  exact h

/-! ## Numeric fixture F-4: capstone constant (`r = 1`, `d = 3`, `L = 2`) -/

/-- **Fixture (capstone constant, `r = 1`, `d = 3`, `L = 2`).** At `h₀ := 5/2`, `o₀ := 1/2` the
capstone's bound `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` evaluates to
`4 · 27 · 125 · (5/2) · (1/4) · 8 = 67500`. This separates the book-solution misprint
`(2r+1)²(4r+1)^d` form (`22500`), the swapped-power forms `4m₁² = 14580` and `4m₂² = 312500`
(`m₁ = 27`, `m₂ = 125`), `8m₁m₂ = 135000`, and the exponent-shape slip `L^d = 8 ≠ d^L = 9`.
Instantiated over abstract `pos, h, o, Φ` constrained only by the capstone's own hypotheses, so
`norm_num` cannot close the goal without invoking the theorem. -/
example (pos : Λ → (Fin 3 → ℤ)) (hpos : Function.Injective pos)
    (h o : Λ → ManyBodyOpS Λ N) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hHloc : ∀ x z : Λ, z ∉ coordSupBall pos 1 x → Commute (h x) (o z))
    (hOloc : ∀ x z : Λ, z ∉ coordSupBall pos 2 x →
      ∀ y ∈ coordSupBall pos 1 x, Commute (o z) (h x * o y - o y * h x))
    (hnh : ∀ x : Λ, manyBodyOperatorNormS (h x) ≤ (5 / 2 : ℝ))
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ (1 / 2 : ℝ))
    (hΛ : (Fintype.card Λ : ℝ) ≤ (2 : ℝ) ^ (3 : ℕ))
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
          - ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
            * (∑ x : Λ, o x)) Φ
      ≤ (67500 : ℝ) := by
  have h' : rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
          - ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
            * (∑ x : Λ, o x)) Φ
      ≤ 4 * (2 * ((1 : ℕ) : ℝ) + 1) ^ (3 : ℕ) * (4 * ((1 : ℕ) : ℝ) + 1) ^ (3 : ℕ) * (5 / 2 : ℝ)
          * (1 / 2 : ℝ) ^ 2 * (((2 : ℕ) : ℝ)) ^ (3 : ℕ) :=
    tasaki_problem_3_4_a_doubleCommutator_expectation_le pos hpos h o 1 2 (5 / 2) (1 / 2)
      hHloc hOloc hnh hno (by norm_num) (by norm_num) hΛ hΦ
  norm_num at h'
  exact h'

end LatticeSystem.Tests.RangeLocalDoubleCommutatorBound
