import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge

/-!
# §10.2.3 Theorem 10.6 — staggered spin component algebra (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismStaggeredAlgebra.lean`.
`example`s pin down the exact signatures of
`fermionStaggeredSpinZ`, `fermionStaggeredTransverse`,
`fermionSpinDot_eq_transverse_add_spinZ_mul`,
`fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq`,
`fermionStaggeredSpinZ_isHermitian`, `vectorExpectation_staggeredSpinZ_sq_nonneg`,
`fermionStaggeredTransverse_expectation_le_staggeredCasimir_expectation` and
`fermionStaggeredCasimirOp_zero_eq_totalSpinSquared`, mirroring the discharged SpinS template
`Quantum/SpinS/FerrimagneticLROComponentAlgebra.lean`, so that the implementation cannot silently
drift from the design's exact statements.  The closing `N = 0` sanity check is the cheapest
falsifier of a staggered-sign or normalization slip: on a single site the staggered gauge squares
to `+1`, so the staggered order parameter collapses to the plain total-spin Casimir.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismStaggeredAlgebra

open LatticeSystem.Fermion LatticeSystem.Quantum
open scoped BigOperators

/-! ## 1. Signature specification: `fermionStaggeredSpinZ`, `fermionStaggeredTransverse` -/

/-- `fermionStaggeredSpinZ` must have the staggered-sign single-sum signature
`Ô^{(3)} = Σ_x ε_x Ŝ^z_x` over `ManyBodyOp (Fin (2N+2))`. -/
noncomputable example (N : ℕ) (A : Finset (Fin (N + 1))) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionStaggeredSpinZ N A

/-- `fermionStaggeredSpinZ` unfolds to `Σ_x (gaugeSign A x) • Ŝ^z_x`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    fermionStaggeredSpinZ N A =
      ∑ x : Fin (N + 1), gaugeSign A x • fermionSiteSpinZ N x := rfl

/-- `fermionStaggeredTransverse` must have the doubly-staggered double-sum signature
`Σ_{x,y} ε_x ε_y · fermionSpinTransverse_{x,y}` over `ManyBodyOp (Fin (2N+2))`. -/
noncomputable example (N : ℕ) (A : Finset (Fin (N + 1))) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionStaggeredTransverse N A

/-- `fermionStaggeredTransverse` unfolds to
`Σ_x Σ_y (gaugeSign A x * gaugeSign A y) • fermionSpinTransverse N x y`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    fermionStaggeredTransverse N A =
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (gaugeSign A x * gaugeSign A y) • fermionSpinTransverse N x y := rfl

/-! ## 2. Per-pair decomposition: `fermionSpinDot_eq_transverse_add_spinZ_mul` -/

/-- **Per-pair split of `Ŝ_x·Ŝ_y`.** The two-site spin dot product decomposes into its
transverse `(1,2)`-plane part plus the longitudinal `Ŝ^z_x Ŝ^z_y` term. -/
example (N : ℕ) (x y : Fin (N + 1)) :
    fermionSpinDot N x y =
      fermionSpinTransverse N x y + fermionSiteSpinZ N x * fermionSiteSpinZ N y :=
  fermionSpinDot_eq_transverse_add_spinZ_mul N x y

/-! ## 3. Staggered-Casimir split:
`fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq` -/

/-- **Transverse / longitudinal split of `(Ô_L)²`** (mirrors Tasaki eq. (4.1.12) / Theorem 10.6's
staggered analogue of (10.2.16)): the squared staggered Casimir operator splits as the staggered
transverse double sum plus the square of the staggered longitudinal operator `Ô^{(3)}`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    fermionStaggeredCasimirOp N A =
      fermionStaggeredTransverse N A + fermionStaggeredSpinZ N A * fermionStaggeredSpinZ N A :=
  fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq N A

/-! ## 4. Hermiticity and positivity -/

/-- `fermionStaggeredSpinZ` is self-adjoint (a real-linear combination of the Hermitian per-site
`Ŝ^z_x`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    (fermionStaggeredSpinZ N A).IsHermitian :=
  fermionStaggeredSpinZ_isHermitian N A

/-- **Hermitian-square positivity.** The expectation of `(Ô^{(3)})²` is nonnegative in every
state vector — the positivity step feeding the ferrimagnetic order-parameter bound. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    0 ≤ (vectorExpectation (fermionStaggeredSpinZ N A * fermionStaggeredSpinZ N A) v).re :=
  vectorExpectation_staggeredSpinZ_sq_nonneg N A v

/-- **Transverse expectation lower bound for `(Ô_L)²`.** Dropping the positive-semidefinite
longitudinal square only decreases the expectation, so the staggered transverse expectation is a
lower bound for the full staggered Casimir expectation. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (vectorExpectation (fermionStaggeredTransverse N A) v).re ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re :=
  fermionStaggeredTransverse_expectation_le_staggeredCasimir_expectation N A v

/-! ## 5. `N = 0` sanity check -/

/-- **`A0b` (PR-8 design §2 layer A): single-site collapse, moved to the library.**  For `N = 0`
the only pair is `x = y = 0`, whose staggered weight is `ε₀ ε₀ = +1` for either sublattice choice,
so the staggered order parameter `(Ô_L)²` is the plain total-spin Casimir `(Ŝ_tot)²`. PR-8's
`N = 0` branch (`E1`, `liebFerrimagnetism_N_zero`) needs this from the library, not the `Tests`
root, so the statement moves to `LiebFerrimagnetismStaggeredAlgebra.lean` (this pin only calls it).
This pin fails to compile until the library declaration lands: re-proving it here while the
library copy also exists would be a banned duplicate statement. -/
example (A : Finset (Fin 1)) :
    fermionStaggeredCasimirOp 0 A = fermionTotalSpinSquared 0 :=
  fermionStaggeredCasimirOp_zero_eq_totalSpinSquared A

/-- **Single-site split.**  The transverse / longitudinal decomposition reproduces `(Ŝ_tot)²` at
`N = 0` for either sublattice choice — a sign or normalization slip in the split would break this
even before any ground-state input. -/
example (A : Finset (Fin 1)) :
    fermionTotalSpinSquared 0 =
      fermionStaggeredTransverse 0 A + fermionStaggeredSpinZ 0 A * fermionStaggeredSpinZ 0 A := by
  rw [← fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq,
    fermionStaggeredCasimirOp_zero_eq_totalSpinSquared]

end LatticeSystem.Tests.LiebFerrimagnetismStaggeredAlgebra
