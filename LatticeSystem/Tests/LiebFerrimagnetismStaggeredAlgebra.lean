import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra

/-!
# §10.2.3 Theorem 10.6 PR-1 — staggered spin component algebra (Red specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 354, eqs. (10.2.16)/(10.2.17).)

TDD **Red** specification for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismStaggeredAlgebra.lean`
(design: `.self-local/docs/theorem-10-6-design.md`, PR-1 bullet list), which does not exist yet.
No `sorry`, no production code — `example`s that pin down the exact signatures of
`fermionStaggeredSpinZ`, `fermionStaggeredTransverse`,
`fermionSpinDot_eq_transverse_add_spinZ_mul`,
`fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq`,
`fermionStaggeredSpinZ_isHermitian`, `vectorExpectation_staggeredSpinZ_sq_nonneg`,
`fermionStaggeredTransverse_expectation_le_staggeredCasimir_expectation` and
`fermionStaggeredCasimirOp_isHermitian`, mirroring the discharged SpinS template
`Quantum/SpinS/FerrimagneticLROComponentAlgebra.lean`, so that PR-1's implementation cannot
silently drift from the design's exact statements.

This file's import alone is expected to fail until PR-1 lands the production module: that failure
*is* the Red state this test suite records.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismStaggeredAlgebra

open LatticeSystem.Fermion LatticeSystem.Quantum Matrix
open scoped BigOperators ComplexOrder

variable {N : ℕ}

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

/-! ## 3. Staggered-Casimir split: `fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq` -/

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

/-- `fermionStaggeredCasimirOp` is self-adjoint (used everywhere downstream to discharge `.im = 0`
on its expectations). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    (fermionStaggeredCasimirOp N A).IsHermitian :=
  fermionStaggeredCasimirOp_isHermitian N A

end LatticeSystem.Tests.LiebFerrimagnetismStaggeredAlgebra
