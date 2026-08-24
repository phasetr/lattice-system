import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredBound

/-!
# §10.2.3 Theorem 10.6 — centered sector `⟨Ô²⟩ ≥ S₀²` lower bound (specification)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismCenteredBound.lean` (PR-7 of the
Theorem 10.6 discharge arc, issue #5347). The `example`s pin the exact type signature (and,
crucially, the exact *hypothesis set*) of the five public declarations per this arc's PR-7
design: the generic sum-linearity of
`vectorExpectation` (`D1`), the sign-transport bound onto the double-sum transverse operator
(`D3`), the Casimir identity on the centered tower member (`D4`), the capstone ratio bound with
**weakest hypotheses** (`D7`, no `hbip`/`hT_conn`/`hU`/`1 ≤ N`), and the existential capstone
consuming PR-6's `liebRepulsive_exists_centered_transverse_sign` (`D8`). Mirrors the specification
style of `Tests/LiebFerrimagnetismCenteredSector.lean` and
`Tests/LiebFerrimagnetismGroundTower.lean`.
`D0`'s de-privatization, and the `private` `D2`/`D5`/`D6` arithmetic/pair-sign lemmas, are not
pinned here (repo convention: only public declarations get a `Tests/` pin).

Notation: `L := sublatticeImbalance A`, `k₀ := L / 2` (ℕ division), `S₀ := L/2 : ℝ`,
`γ₀ := liebRepulsiveSpinCasimir A`, `u := ((fermionTotalSpinMinus N) ^ k₀).mulVec w`,
`Ô² := fermionStaggeredCasimirOp N A`.

The closing section pins the design's cheapest possible sign-direction counter-check
(design §5, "符号の向き"): flipping the sign of a strictly negative real makes it strictly
positive and equal to its absolute value, as pure `ℝ` arithmetic (no state vector needed) —
the shape `D2`'s off-sublattice branch (`gaugeSign` product `= -1`) relies on.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismCenteredBound

open Matrix Module LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math

/-! ## `D1` — sum-linearity of `vectorExpectation` -/

/-- **`D1`: `vectorExpectation` is additive over a `Finset` sum of observables.** Generic in the
index types `ι` (the carrier, `Fintype`) and `κ` (the summation index); no model hypotheses. -/
example {ι κ : Type*} [Fintype ι] (s : Finset κ) (O : κ → Matrix ι ι ℂ) (v : ι → ℂ) :
    vectorExpectation (∑ k ∈ s, O k) v = ∑ k ∈ s, vectorExpectation (O k) v :=
  vectorExpectation_sum s O v

/-! ## `D3` — sign step: double-sum transverse operator ≤ staggered transverse operator -/

/-- **`D3`: the double-sum transverse expectation is `≤` the staggered transverse expectation.**
Takes **no model hypotheses** (no `hbip`/`hT_conn`/`hU`/`1 ≤ N`): the sign pattern `hsign` is
passed in verbatim in PR-6's exact shape (`T5`'s conclusion), so the bound is pure sign-and-sum
bookkeeping independent of how the sign pattern was established. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsign : ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y) v).im = 0 ∧
        (SameSublattice A x y → 0 < (vectorExpectation (fermionSpinTransverse N x y) v).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y) v).re < 0)) :
    (vectorExpectation (∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y) v).re ≤
      (vectorExpectation (fermionStaggeredTransverse N A) v).re :=
  liebRepulsive_centered_staggeredTransverse_ge_sum A v hsign

/-! ## `D4` — Casimir identity on the centered tower member -/

/-- **`D4`: the double-sum transverse expectation on the centered tower member equals the
Casimir gap `(γ₀ − m₀²)` times the squared tower-member norm.** Complex-valued (no `.re` yet). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    vectorExpectation (∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y)
        (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)
      = (liebRepulsiveSpinCasimir A
          - ((sublatticeImbalance A : ℂ) / 2 - ((sublatticeImbalance A / 2 : ℕ) : ℂ)) ^ 2)
        * (star (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w) ⬝ᵥ
            ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w) :=
  liebRepulsive_centered_sum_transverse_eq N A T hT U E₀ (hcas := hcas) (hwG := hwG) (hz := hz)

/-! ## `D7` — capstone ratio bound (weakest hypotheses) -/

/-- **`D7`: `S₀² ≤ ⟨Ô²⟩.re / ‖u‖²` on the centered tower member `u`, weakest hypotheses.** Takes
**no** `hbip`/`hT_conn`/`hU`/`1 ≤ N` (the sign pattern is passed in as `hsign`, PR-6's exact
shape at `u`); the denominator `star u ⬝ᵥ u` is exposed in the PR-4-style unfolded form. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (hsign : ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
        (SameSublattice A x y →
            0 < (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0)) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re /
        (star (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w) ⬝ᵥ
            ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w).re :=
  liebRepulsive_centered_ratioRe_ge_sq N A T hT U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (hz := hz) (hsign := hsign)

/-! ## `D8` — existential capstone -/

/-- **`D8`: existential centered-sector `⟨Ô²⟩ ≥ S₀²` bound.** Consumes PR-6's
`liebRepulsive_exists_centered_transverse_sign` (`T6`), so it carries the **full** Theorem 10.5
model hypotheses (`hbip`, `hT_conn`, `hU`, `1 ≤ N`) that `D7` deliberately omits — the arc's
existing PR-6 reference-0 debt is cleared here rather than deferred to PR-8. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (hN : 1 ≤ N) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) :
    ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, w ≠ 0 ∧
      w ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ∧
      (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w ∧
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
        (vectorExpectation (fermionStaggeredCasimirOp N A)
            (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re /
          (star (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w) ⬝ᵥ
              ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w).re :=
  liebRepulsive_exists_centered_ratioRe_ge_sq N A T hT hbip hT_conn U hU hN E₀ (hne := hne)
    (hmin := hmin) (hcas := hcas)

/-! ## Sign-direction sanity check (design §5, independent of any state vector) -/

/-- **Cheapest sign-direction counter-check.** Flipping the sign of a strictly negative real
makes it strictly positive and equal to its absolute value — the pure-`ℝ` shape `D2`'s
off-sublattice branch (`gaugeSign A x * gaugeSign A y = -1`) relies on: multiplying a
strictly-negative expectation `r` by `-1` yields `-r = |r| > 0`. -/
example (r : ℝ) (hr : r < 0) : 0 < (-1 : ℝ) * r ∧ (-1 : ℝ) * r = |r| := by
  constructor
  · nlinarith
  · rw [abs_of_neg hr]; ring

end LatticeSystem.Tests.LiebFerrimagnetismCenteredBound
