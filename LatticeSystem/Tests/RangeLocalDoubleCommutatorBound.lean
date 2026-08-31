import LatticeSystem.Quantum.SpinS.RangeLocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra

/-!
# Test coverage for the general range-`r` bound, Problem 3.4.a, eq. (3.4.13)

Fixtures for the rewritten `LatticeSystem/Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean`
(honest support-predicate form), the new `LatticeSystem/Math/Combinatorics/SiteBall.lean`, and the
new `LatticeSystem/Quantum/SpinS/TorusSupDistance.lean`, plus the extension of
`LatticeSystem/Quantum/SpinS/RingDistance.lean`. Reference: H. Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems* (1st ed., Springer, 2020), §3.4, Problem 3.4.a, statement pp. 67-68,
printed solution p. 501.

The capstone `tasaki_problem_3_4_a_doubleCommutator_expectation_le` exists only in its
support-predicate form: there is no hypothesis-form declaration of that name for these pins to
resolve against.

## What each block pins

**Kept from PR-4 (unchanged production code).** `coordSupBall`, `mem_coordSupBall`,
`card_coordSupBall_le` (`Math/Combinatorics/CoordinateBall.lean`) and the two-window collapse /
kernel (`doubleCommutator_orderSum_eq_twoWindowSum`,
`manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows`,
`Quantum/SpinS/LocalDoubleCommutatorBound.lean`) are re-pinned as-is; F-2 (the `Fin 2 → Fin 3`
tightness fixture) and F-3 (the two-window kernel constant) are kept as-is.

**New signature pins.** `siteBall`, `mem_siteBall`, `disjoint_siteBall_of_lt`
(`Math/Combinatorics/SiteBall.lean`); `ringDist_comm`, `ringDist_self`, `ringDist_triangle`,
`signedRingDisp_self`, `signedRingDisp_injective` (extension of
`Quantum/SpinS/RingDistance.lean`); `torusSupDist`, `torusSupDist_le_iff`, `torusSupDist_comm`,
`torusSupDist_triangle`, `card_siteBall_torusSupDist_le`
(`Quantum/SpinS/TorusSupDistance.lean`); and
`manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal` together with the rewritten capstone
`tasaki_problem_3_4_a_doubleCommutator_expectation_le`
(`Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean`), whose locality hypotheses are now
`SupportedOnS`-based rather than raw commutation hypotheses.

**New numeric fixtures.**
- F-1 (periodic wraparound, `by decide`): on the torus `Fin 2 → Fin 5`, the sup-distance from the
  origin to the antipode-by-coordinate `fun _ => 4` is `1` (the *cyclic* arc `4 → 0`, length `1`,
  not the linear gap `4`), and the radius-`1` ball around the origin contains `fun _ => 4` but not
  `fun _ => 2`. A non-periodic coordinate ball would instead give distance `4` and exclude
  `fun _ => 4`, so this fixture is exactly what makes periodicity load-bearing.
- F-2' (ball-count tightness, `d = 2`, `r = 1`, `L = 5`, `by decide`): the radius-`1` ball around
  the origin has exactly `9 = (2·1+1)^2` sites, out of `|Λ| = 5^2 = 25`, so the bound is attained
  and locality is non-trivial (`9 < 25`).
- F-4′ (capstone constant, `r = 1`, `d = 2`, `L = 5`, `h₀ = 2`, `o₀ = 1/2`): the correct bound
  `4(4r+1)^d(8r+1)^d h₀ o₀² L^d` evaluates to `4·25·81·2·(1/4)·25 = 101250`, discriminated from the
  book-solution printed-constant form `4(2r+1)^d(4r+1)^d h₀ o₀² L^d = 4·9·25·2·(1/4)·25 = 11250`
  and from the exponent-shape slip `L^d = 25 ≠ d^L = 32`.
- F-5 (premise witness): a concrete `Λ = Fin 2 → Fin 5`, `N = 1`, `r = 1` instance — order term
  `o x := onSiteS x (spinSOp3 1)` (`o₀ = 1/2`) and Hamiltonian term
  `h x := onSiteS x (spinSOp1 1) + onSiteS (shift x) (spinSOp1 1)` with
  `shift x := Function.update x 0 (x 0 + 1)` (`h₀ = 2`, support = **2** sites, wrapping the ring
  coordinate) — whose `SupportedOnS` hypotheses are **discharged by proof**
  (`supportedOnS_onSiteS`, `SupportedOnS.add`, `ringDist_self`, and `∀ a : Fin 5,
  ringDist 5 (a + 1) a = 1` by `decide`), not assumed. No prior test ever witnessed the range-`r`
  locality hypotheses being jointly satisfiable in a non-degenerate (non-singleton-support, ball
  ⊊ `Λ`, wrapping) way.

## Coverage limits (stated honestly)

The kernel and capstone fixtures (F-3, F-4′) discriminate the constant only while the library
statement and the fixture's intermediate `have` are not both changed to the *same* wrong constant
at once. `4 m₁ m₂` is symmetric in `m₁` and `m₂`, so **no numeric fixture on the constant alone can
detect an `m₁ ↔ m₂` swap** (the inner-`r`/outer-`2r` window swap). In this rewritten,
`SupportedOnS`-based form what pins the window roles is **provability**, not a fixture: assembling
the swapped windows into `manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal`'s `hWW`
obligation (`∀ x ∉ (outer ball), ∀ z ∈ (inner ball), Commute (o x) (h b * o z - o z * h b)`)
requires deriving `2 * r < dist x z` from `4 * r < dist x b` and `dist z b ≤ 2 * r`, which needs
the outer ball to be the *wider* one; with the windows swapped this derivation is not available
and the proof does not go through. This is a **provability** claim, not an
unprovability-*by-*obligation claim in the old hypothesis-form sense: the argument above does not
hold for the hypothesis form of the capstone and must not be restated for it.
-/

namespace LatticeSystem.Tests.RangeLocalDoubleCommutatorBound

open LatticeSystem
open LatticeSystem.Quantum
open LatticeSystem.Math
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Kept from PR-4: signature pins on `Math/Combinatorics/CoordinateBall.lean` -/

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

/-! ## Kept from PR-4: signature pins on the two-window core -/

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

/-! ## New signature pins: `Math/Combinatorics/SiteBall.lean` -/

/-- **Signature pin (`siteBall`).** `siteBall dist r x = {y : dist y x ≤ r}` for an abstract
distance function `dist : Λ → Λ → ℕ`, generalising `coordSupBall` off the coordinate embedding. -/
example (dist : Λ → Λ → ℕ) (r : ℕ) (x : Λ) :
    siteBall dist r x = Finset.univ.filter fun y => dist y x ≤ r := by
  rfl

/-- **Signature pin (`mem_siteBall`).** Membership unfolds to the distance bound. -/
example {dist : Λ → Λ → ℕ} {r : ℕ} {x y : Λ} :
    y ∈ siteBall dist r x ↔ dist y x ≤ r :=
  mem_siteBall

/-- **Signature pin (`disjoint_siteBall_of_lt`).** Balls of radius `r` around sites more than
`2r` apart (w.r.t. a symmetric triangle-inequality-satisfying `dist`) are disjoint. -/
example {dist : Λ → Λ → ℕ} (hsymm : ∀ a b, dist a b = dist b a)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c) {r : ℕ} {x y : Λ} (h : 2 * r < dist x y) :
    Disjoint (siteBall dist r x) (siteBall dist r y) :=
  disjoint_siteBall_of_lt hsymm htri h

/-! ## New signature pins: the `RingDistance.lean` extension -/

/-- **Signature pin (`ringDist_comm`).** The ring distance is symmetric. -/
example (L : ℕ) (x y : Fin L) : ringDist L x y = ringDist L y x :=
  ringDist_comm L x y

/-- **Signature pin (`ringDist_self`).** The ring distance from a site to itself is `0`. -/
example (L : ℕ) (x : Fin L) : ringDist L x x = 0 :=
  ringDist_self L x

/-- **Signature pin (`ringDist_triangle`).** The ring distance satisfies the triangle
inequality. -/
example (L : ℕ) (x y z : Fin L) : ringDist L x z ≤ ringDist L x y + ringDist L y z :=
  ringDist_triangle L x y z

/-- **Signature pin (`signedRingDisp_self`).** The signed cyclic displacement of a site to itself
vanishes. -/
example (L : ℕ) (x : Fin L) : signedRingDisp L x x = 0 :=
  signedRingDisp_self L x

/-- **Signature pin (`signedRingDisp_injective`).** For fixed `x`, `y ↦ signedRingDisp L x y` is
injective (needed to pull the sup-distance ball count back to `card_coordSupBall_le`). -/
example (L : ℕ) (x : Fin L) : Function.Injective (signedRingDisp L x) :=
  signedRingDisp_injective L x

/-! ## New signature pins: `Quantum/SpinS/TorusSupDistance.lean` -/

/-- **Signature pin (`torusSupDist`).** The sup-norm of per-coordinate ring distances on the
`d`-torus `Fin d → Fin L`. -/
example (d L : ℕ) (x y : Fin d → Fin L) :
    torusSupDist d L x y = Finset.univ.sup fun i => ringDist L (x i) (y i) := by
  rfl

/-- **Signature pin (`torusSupDist_le_iff`).** The sup-distance bound is coordinate-wise. -/
example {d L : ℕ} {x y : Fin d → Fin L} {r : ℕ} :
    torusSupDist d L x y ≤ r ↔ ∀ i, ringDist L (x i) (y i) ≤ r :=
  torusSupDist_le_iff

/-- **Signature pin (`torusSupDist_comm`).** The torus sup-distance is symmetric. -/
example (d L : ℕ) (x y : Fin d → Fin L) : torusSupDist d L x y = torusSupDist d L y x :=
  torusSupDist_comm d L x y

/-- **Signature pin (`torusSupDist_triangle`).** The torus sup-distance satisfies the triangle
inequality. -/
example (d L : ℕ) (x y z : Fin d → Fin L) :
    torusSupDist d L x z ≤ torusSupDist d L x y + torusSupDist d L y z :=
  torusSupDist_triangle d L x y z

/-- **Signature pin (`card_siteBall_torusSupDist_le`).** `|B_r(x)| ≤ (2r+1)^d` for the torus
sup-distance ball, matching `card_coordSupBall_le`'s bound with no injectivity hypothesis needed
(periodicity supplies it via `signedRingDisp_injective`). -/
example (d L r : ℕ) (x : Fin d → Fin L) :
    (siteBall (torusSupDist d L) r x).card ≤ (2 * r + 1) ^ d :=
  card_siteBall_torusSupDist_le d L r x

/-! ## New signature pins: the rewritten `RangeLocalDoubleCommutatorBound.lean` -/

/-- **Signature pin (`manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal`).** The abstract
range-`r` norm bound over any symmetric, triangle-inequality-satisfying distance `dist`, with
`SupportedOnS`-based (not commutation-based) locality hypotheses `hsh`, `hso`. -/
example (dist : Λ → Λ → ℕ) (hsymm : ∀ a b, dist a b = dist b a)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (h o : Λ → ManyBodyOpS Λ N) (r : ℕ) (h₀ o₀ : ℝ) (m₁ m₂ : ℕ)
    (hsh : ∀ x, SupportedOnS (siteBall dist r x) (h x))
    (hso : ∀ x, SupportedOnS (siteBall dist r x) (o x))
    (hnh : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hm₁ : ∀ b : Λ, (siteBall dist (2 * r) b).card ≤ m₁)
    (hm₂ : ∀ b : Λ, (siteBall dist (4 * r) b).card ≤ m₂) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b : Λ, h b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b : Λ, h b))
          - ((∑ b : Λ, h b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b : Λ, h b))
            * (∑ x : Λ, o x))
      ≤ 4 * (m₁ : ℝ) * (m₂ : ℝ) * h₀ * o₀ ^ 2 * (Fintype.card Λ : ℝ) :=
  manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal
    dist hsymm htri h o r h₀ o₀ m₁ m₂ hsh hso hnh hno ho₀ hm₁ hm₂

/-- **Signature pin (eq. (3.4.13) capstone, honest support form).** No `pos`/injectivity, no
`hΛ : |Λ| ≤ L^d` slack hypothesis — `Λ` is fixed to the periodic torus `Fin d → Fin L`, and
locality is a genuine `SupportedOnS` condition rather than a commutation hypothesis. -/
example {d L : ℕ} (h o : (Fin d → Fin L) → ManyBodyOpS (Fin d → Fin L) N) (r : ℕ) (h₀ o₀ : ℝ)
    {Φ : ((Fin d → Fin L) → Fin (N + 1)) → ℂ}
    (hsh : ∀ x, SupportedOnS (siteBall (torusSupDist d L) r x) (h x))
    (hso : ∀ x, SupportedOnS (siteBall (torusSupDist d L) r x) (o x))
    (hnh : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x, o x) * ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b))
          - ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b)) * (∑ x, o x)) Φ
      ≤ 4 * (4 * (r : ℝ) + 1) ^ d * (8 * (r : ℝ) + 1) ^ d * h₀ * o₀ ^ 2 * (L : ℝ) ^ d :=
  tasaki_problem_3_4_a_doubleCommutator_expectation_le d L N r h o h₀ o₀ hsh hso hnh hno ho₀ hΦ

/-! ## Numeric fixture F-1: periodic wraparound (`d = 2`, `L = 5`, `by decide`) -/

/-- **Fixture (periodic wraparound, sup-distance).** The torus sup-distance from the origin to
`fun _ => 4` on `Fin 2 → Fin 5` is the *cyclic* arc length `1` (`4 → 0`), not the linear gap `4`: a
non-periodic coordinate ball would instead give distance `4`. -/
example : torusSupDist 2 5 (fun _ => (0 : Fin 5)) (fun _ => (4 : Fin 5)) = 1 := by decide

/-- **Fixture (periodic wraparound, membership).** The wrapping site `fun _ => 4` lies in the
radius-`1` ball around the origin, exactly because the wraparound distance is `1`. -/
example : (fun _ => (4 : Fin 5)) ∈ siteBall (torusSupDist 2 5) 1 (fun _ => (0 : Fin 5)) := by
  decide

/-- **Fixture (periodic wraparound, non-membership).** The site `fun _ => 2` (linear distance `2`,
also the cyclic distance, since `5 - 2 = 3 > 2`) is excluded from the same ball. -/
example : (fun _ => (2 : Fin 5)) ∉ siteBall (torusSupDist 2 5) 1 (fun _ => (0 : Fin 5)) := by
  decide

/-! ## Numeric fixtures F-2 (kept) and F-2' (new): ball-count tightness
(`d = 2`, `r = 1`, `L = 5`) -/

/-- **Fixture (kept, `coordSupBall` tightness, `Fin 2 → Fin 3`).** As in PR-4: every site lies in
the radius-`1` ball, so `coordSupBall pos 1 c = Finset.univ`, of card `9 = (2·1+1)^2`, forcing an
equality (not just a one-sided bound) through `le_antisymm`. -/
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

/-- **Fixture F-2' (new, `siteBall`/`torusSupDist` tightness, `d = 2`, `r = 1`, `L = 5`,
`by decide`).**
The radius-`1` ball around the origin on the `d = 2`, `L = 5` torus has exactly
`9 = (2·1+1)^2` sites (the bound is attained), out of `|Λ| = 25`, so locality is non-trivial:
`9 < 25`. -/
example : (siteBall (torusSupDist 2 5) 1 (fun _ => (0 : Fin 5))).card = 9 := by decide

/-- Companion half of the previous fixture: the ball is a *proper* subset of `Λ`, i.e. locality is
non-vacuous at these parameters. -/
example : (siteBall (torusSupDist 2 5) 1 (fun _ => (0 : Fin 5))).card < Fintype.card (Fin 2 → Fin 5)
    := by decide

/-! ## Numeric fixture F-3: two-window kernel constant (`m₁ ≠ m₂`, kept as-is) -/

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

/-! ## Numeric fixture F-4′: capstone constant (`r = 1`, `d = 2`, `L = 5`) -/

/-- **Fixture (capstone constant, `r = 1`, `d = 2`, `L = 5`, `h₀ = 2`, `o₀ = 1/2`).** The
capstone's bound `4 (4r+1)^d (8r+1)^d h₀ o₀² L^d` evaluates to `4·25·81·2·(1/4)·25 = 101250`. This
separates the book-solution printed-constant form `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`
(`4·9·25·2·(1/4)·25 = 11250`), and the exponent-shape slip `L^d = 25 ≠ d^L = 32`. Instantiated over
abstract `h, o, Φ` constrained only by the capstone's own hypotheses, so `norm_num` cannot close
the goal without invoking the theorem. -/
example (h o : (Fin 2 → Fin 5) → ManyBodyOpS (Fin 2 → Fin 5) N)
    {Φ : ((Fin 2 → Fin 5) → Fin (N + 1)) → ℂ}
    (hsh : ∀ x, SupportedOnS (siteBall (torusSupDist 2 5) 1 x) (h x))
    (hso : ∀ x, SupportedOnS (siteBall (torusSupDist 2 5) 1 x) (o x))
    (hnh : ∀ x, manyBodyOperatorNormS (h x) ≤ (2 : ℝ))
    (hno : ∀ x, manyBodyOperatorNormS (o x) ≤ (1 / 2 : ℝ))
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x, o x) * ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b))
          - ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b)) * (∑ x, o x)) Φ
      ≤ (101250 : ℝ) := by
  have h' : rayleighOnVec
        ((∑ x, o x) * ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b))
          - ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b)) * (∑ x, o x)) Φ
      ≤ 4 * (4 * ((1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) * (8 * ((1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) * (2 : ℝ)
          * (1 / 2 : ℝ) ^ 2 * (((5 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    tasaki_problem_3_4_a_doubleCommutator_expectation_le 2 5 N 1 h o 2 (1 / 2)
      hsh hso hnh hno (by norm_num) hΦ
  norm_num at h'
  exact h'

/-! ## Numeric fixture F-5: a witness jointly satisfying the range-`r` premises -/

/-- **Fixture (premise witness, `Λ = Fin 2 → Fin 5`, `N = 1`, `r = 1`).** The site-`0`-and-shifted
Hamiltonian term `h x := onSiteS x (spinSOp1 1) + onSiteS (shift x) (spinSOp1 1)`, with
`shift x := Function.update x 0 (x 0 + 1)`, is `SupportedOnS` on `{x, shift x}` — two sites, one
of them reached by *wrapping* the ring coordinate — a support **upper bound**, not a proof that
the support is exactly these two sites. Both sites lie in the radius-`1` ball around `x`, since
`ringDist 5 (x 0 + 1) (x 0) = 1` and every other coordinate contributes distance `0`
(`ringDist_self`). The order term `o x := onSiteS x (spinSOp3 1)` has singleton support `{x}`. The
norm bounds `h₀ = 2`, `o₀ = 1/2` come from `onSiteS_spinSOp1_manyBodyOperatorNormS_le` (triangle
inequality over the two-term sum) and `onSiteS_spinSOp3_manyBodyOperatorNormS_le`. No hypothesis of
the capstone is discharged by `sorry` or assumed abstractly: every one is proved from this concrete
data. -/
example {Φ : ((Fin 2 → Fin 5) → Fin 2) → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))
            * ((∑ b, (onSiteS b (spinSOp1 1)
                    + onSiteS (Function.update b 0 (b 0 + 1)) (spinSOp1 1)))
                * (∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))
              - (∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))
                * (∑ b, (onSiteS b (spinSOp1 1)
                    + onSiteS (Function.update b 0 (b 0 + 1)) (spinSOp1 1))))
          - ((∑ b, (onSiteS b (spinSOp1 1)
                    + onSiteS (Function.update b 0 (b 0 + 1)) (spinSOp1 1)))
                * (∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))
              - (∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))
                * (∑ b, (onSiteS b (spinSOp1 1)
                    + onSiteS (Function.update b 0 (b 0 + 1)) (spinSOp1 1))))
            * (∑ x, (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1))) Φ
      ≤ (101250 : ℝ) := by
  have hring : ∀ a : Fin 5, ringDist 5 (a + 1) a = 1 := by decide
  have hself : ∀ x : Fin 2 → Fin 5, x ∈ siteBall (torusSupDist 2 5) 1 x := fun x =>
    mem_siteBall.mpr (torusSupDist_le_iff.mpr fun i => by rw [ringDist_self]; exact Nat.zero_le 1)
  have hshift : ∀ x : Fin 2 → Fin 5,
      Function.update x 0 (x 0 + 1) ∈ siteBall (torusSupDist 2 5) 1 x := by
    intro x
    refine mem_siteBall.mpr (torusSupDist_le_iff.mpr fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_self]
      exact le_of_eq (hring (x 0))
    · rw [Function.update_of_ne hi, ringDist_self]
      exact Nat.zero_le 1
  have hsh : ∀ x : Fin 2 → Fin 5,
      SupportedOnS (siteBall (torusSupDist 2 5) 1 x)
        ((onSiteS x (spinSOp1 1)
            + onSiteS (Function.update x 0 (x 0 + 1)) (spinSOp1 1) :
              ManyBodyOpS (Fin 2 → Fin 5) 1)) := fun x =>
    SupportedOnS.add (supportedOnS_onSiteS (hself x) (spinSOp1 1))
      (supportedOnS_onSiteS (hshift x) (spinSOp1 1))
  have hso : ∀ x : Fin 2 → Fin 5,
      SupportedOnS (siteBall (torusSupDist 2 5) 1 x)
        (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1) := fun x =>
    supportedOnS_onSiteS (hself x) (spinSOp3 1)
  have hnh : ∀ x : Fin 2 → Fin 5,
      manyBodyOperatorNormS
          ((onSiteS x (spinSOp1 1) + onSiteS (Function.update x 0 (x 0 + 1)) (spinSOp1 1) :
              ManyBodyOpS (Fin 2 → Fin 5) 1)) ≤ (2 : ℝ) := by
    intro x
    refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
    have h1 := onSiteS_spinSOp1_manyBodyOperatorNormS_le (N := 1) x (le_refl 1)
    have h2 := onSiteS_spinSOp1_manyBodyOperatorNormS_le (N := 1)
      (Function.update x 0 (x 0 + 1)) (le_refl 1)
    push_cast at h1 h2
    linarith
  have hno : ∀ x : Fin 2 → Fin 5,
      manyBodyOperatorNormS
        (onSiteS x (spinSOp3 1) : ManyBodyOpS (Fin 2 → Fin 5) 1) ≤ (1 / 2 : ℝ) :=
    fun x => by
      have := onSiteS_spinSOp3_manyBodyOperatorNormS_le (N := 1) x
      push_cast at this
      linarith
  refine le_trans (tasaki_problem_3_4_a_doubleCommutator_expectation_le 2 5 1 1
    (fun b => onSiteS b (spinSOp1 1) + onSiteS (Function.update b 0 (b 0 + 1)) (spinSOp1 1))
    (fun x => onSiteS x (spinSOp3 1)) 2 (1 / 2) hsh hso hnh hno (by norm_num) hΦ) ?_
  norm_num

end LatticeSystem.Tests.RangeLocalDoubleCommutatorBound
