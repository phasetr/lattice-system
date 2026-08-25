import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuPairAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiu
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCorrelation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSpinOp
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem

/-!
# Test coverage for the Theorem 10.8 pair/ladder algebra (PR-4)

Pins the API contract of PR-4 of the Theorem 10.8 discharge (design report
`.self-local/docs/theorem-10-8-design.md` §1 "New file `LiebShenQiuPairAlgebra.lean`"),
against `LatticeSystem/Fermion/JordanWigner/Hubbard/LiebShenQiuPairAlgebra.lean`.

1. **PA1** `totalPairCreationOperator_eq_conjTranspose` — `b̂† = b̂ᴴ` (generalizing the former
   inline `hPadj` block, now removed).
2. **PA2** `totalPairCorrelationOperator_eq_sum` — `b̂†b̂ = Σ_{x,y} hubbardPairCorrelationOp N x y`
   (definitional after `Finset.sum_mul_sum` + `mul_assoc`).
3. **PA3** `fermionTotalSpinPlusMinus_eq_sum` — `Ŝ⁺Ŝ⁻ = Σ_{x,y} Ŝ⁺_x Ŝ⁻_y` (same
   double-sum expansion for the per-site ladder operators).
4. **PA4** `shiba_spinPlusMinus_expectation_eq_signed_sum` — the Shiba-transported expectation
   `⟨ψ|Ŝ⁺Ŝ⁻|ψ⟩ = Σ_{x,y} ε_x ε_y ⟨φ|pair x y|φ⟩`, reusing the already-public
   `euclideanExpectation_shiba_conj`/`_smul` helpers (PR-1) and this PR's own
   `euclideanExpectation_sum` helper (used twice), plus
   `shibaSignedUnitary_conj_spinPlusMinus` (`LiebRepulsiveShibaSpinOp.lean:339`).
5. **PA5** `gaugeSign_mul_re_mul_le_of_pos` — the term-wise sign bound `ε_x ε_y · p ≤ p` for `p > 0`
   (uses `gaugeSign_mul_sameSublattice`/`_not_sameSublattice`,
   `LiebRepulsiveCorrelation.lean:83/97`).
6. **PA6** `liebShenQiuPairLowerBound_le_casimir_gap` — the real arithmetic
   `(a−n)(n−b) ≤ S₀(S₀+1) − m(m−1)` under `b ≤ n ≤ a`.
7. **PA7** `liebShenQiu_towerExponent_le_sublatticeImbalance` — the tower-exponent upper bound
   `k = |A| − Ne/2 ≤ sublatticeImbalance A` (design's "N1 resolution": makes the PR-3 hypothesis
   `hk : k ≤ sublatticeImbalance A` dischargeable from the same `b ≤ n ≤ a` side conditions).

Each `example` fails to elaborate unless the corresponding declaration exists, is public, and has
exactly this signature.

**Not covered here**: the capstone assembly and the `Ne = 2(N+1)` degenerate branch (PR-5).
-/

namespace LatticeSystem.Tests.LiebShenQiuPairAlgebra

open LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Pins **PA1**: the total pair creation operator is the conjugate transpose of the total pair
annihilation operator, `b̂† = b̂ᴴ`. -/
example (N : ℕ) :
    totalPairCreationOperator N = Matrix.conjTranspose (totalPairAnnihilationOperator N) :=
  totalPairCreationOperator_eq_conjTranspose N

/-- Pins **PA2**: the total pair-correlation operator expands as the double sum of on-site
pair-transfer operators, `b̂†b̂ = Σ_{x,y} hubbardPairCorrelationOp N x y`. -/
example (N : ℕ) :
    totalPairCorrelationOperator N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), hubbardPairCorrelationOp N x y :=
  totalPairCorrelationOperator_eq_sum N

/-- Pins **PA3**: the total ladder product `Ŝ⁺Ŝ⁻` expands as the double sum of per-site ladder
products. -/
example (N : ℕ) :
    fermionTotalSpinPlus N * fermionTotalSpinMinus N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          fermionSiteSpinPlus N x * fermionSiteSpinMinus N y :=
  fermionTotalSpinPlusMinus_eq_sum N

/-- Pins **PA4**: the Shiba-transported expectation of `Ŝ⁺Ŝ⁻` equals the sublattice-gauge-signed
sum of the on-site pair-correlation expectations, `⟨ψ|Ŝ⁺Ŝ⁻|ψ⟩ = Σ_{x,y} ε_x ε_y ⟨φ|pair x y|φ⟩`. -/
example (N : ℕ) (A : Finset (Fin (N + 1)))
    (φ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp) :
    euclideanExpectation (fermionTotalSpinPlus N * fermionTotalSpinMinus N) ψ
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y)
            * euclideanExpectation (hubbardPairCorrelationOp N x y) φ :=
  shiba_spinPlusMinus_expectation_eq_signed_sum N A φ ψ hψ

/-- Pins **PA5**: the sublattice-gauge sign bounds a strictly positive quantity above by itself,
`(ε_x ε_y).re · p ≤ p` for `p > 0` (used term-wise in the signed-sum-vs-plain-sum comparison). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) {p : ℝ} (hp : 0 < p) :
    (gaugeSign A x * gaugeSign A y).re * p ≤ p :=
  gaugeSign_mul_re_mul_le_of_pos A x y hp

/-- Pins **PA6**: the real-arithmetic inequality `(a−n)(n−b) ≤ S₀(S₀+1) − m(m−1)` between
`liebShenQiuPairLowerBound` and the Casimir/spin-`z` gap, under `b ≤ n ≤ a`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (Ne : ℕ)
    (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) :
    liebShenQiuPairLowerBound A Ne
      ≤ (liebRepulsiveSpinCasimir A).re
        - (((Ne : ℝ) - ((N : ℝ) + 1)) / 2) * ((((Ne : ℝ) - ((N : ℝ) + 1)) / 2) - 1) :=
  liebShenQiuPairLowerBound_le_casimir_gap N A Ne hb ha

/-- Pins **PA7** (N1 resolution): the tower exponent `k = |A| − Ne/2` never exceeds the sublattice
imbalance `L = sublatticeImbalance A`, under the same `b ≤ n ≤ a` side conditions used by PR-3's
tower-pinch hypothesis `hk`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (Ne : ℕ)
    (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) :
    A.card - Ne / 2 ≤ sublatticeImbalance A :=
  liebShenQiu_towerExponent_le_sublatticeImbalance N A Ne hb ha

end LatticeSystem.Tests.LiebShenQiuPairAlgebra
