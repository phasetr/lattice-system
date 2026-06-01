import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Tasaki Problem 2.5.d: bipartite correlation sign bridge

This module starts the Problem 2.5.d correlation-sign formalization by
isolating the final sign-conversion step in Tasaki's solution.  If the
Marshall-gauge-signed two-spin correlation has positive real part, then the
original two-spin correlation is positive on same-sublattice pairs and negative
on cross-sublattice pairs.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution p. 498, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Two-spin correlation and bipartite gauge sign -/

/-- The two-spin correlation expectation
`⟨Φ, (Ŝ_x · Ŝ_y) Φ⟩` for a spin-`S` many-body state. -/
noncomputable def twoSpinCorrelationS (x y : V)
    [Fintype V] [DecidableEq V]
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ) ((spinSDot x y N).mulVec Φ)

/-- The bipartite Marshall-gauge sign: `+1` on `A` and `-1` on its complement. -/
def bipartiteGaugeSign (A : V → Bool) (x : V) : ℂ :=
  if A x then 1 else -1

/-- The product of bipartite gauge signs is `+1` on same-sublattice pairs. -/
theorem bipartiteGaugeSign_mul_eq_one_of_same
    (A : V → Bool) {x y : V} (hxy : A x = A y) :
    bipartiteGaugeSign A x * bipartiteGaugeSign A y = 1 := by
  unfold bipartiteGaugeSign
  rw [← hxy]
  by_cases hx : A x <;> simp [hx]

/-- The product of bipartite gauge signs is `-1` on cross-sublattice pairs. -/
theorem bipartiteGaugeSign_mul_eq_neg_one_of_ne
    (A : V → Bool) {x y : V} (hxy : A x ≠ A y) :
    bipartiteGaugeSign A x * bipartiteGaugeSign A y = -1 := by
  unfold bipartiteGaugeSign
  by_cases hx : A x <;> by_cases hy : A y <;> simp [hx, hy] at hxy ⊢

/-! ## Problem 2.5.d sign conversion -/

/-- Same-sublattice sign half of Problem 2.5.d: if the bipartite-gauge-signed
two-spin correlation has positive real part, then the original two-spin
correlation has positive real part for `A x = A y`. -/
theorem twoSpinCorrelationS_re_pos_of_same_of_bipartite_signed_re_pos
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} {Φ : (V → Fin (N + 1)) → ℂ}
    (hpos : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φ).re)
    (hxy : A x = A y) :
    0 < (twoSpinCorrelationS x y Φ).re := by
  rw [bipartiteGaugeSign_mul_eq_one_of_same A hxy, one_mul] at hpos
  exact hpos

/-- Cross-sublattice sign half of Problem 2.5.d: if the bipartite-gauge-signed
two-spin correlation has positive real part, then the original two-spin
correlation has negative real part for `A x ≠ A y`. -/
theorem twoSpinCorrelationS_re_neg_of_ne_of_bipartite_signed_re_pos
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} {Φ : (V → Fin (N + 1)) → ℂ}
    (hpos : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φ).re)
    (hxy : A x ≠ A y) :
    (twoSpinCorrelationS x y Φ).re < 0 := by
  rw [bipartiteGaugeSign_mul_eq_neg_one_of_ne A hxy] at hpos
  simpa using hpos

/-- Boolean-case packaging of Problem 2.5.d's sign conclusion from the
bipartite-gauge-signed positivity input. -/
theorem twoSpinCorrelationS_sign_cases_of_bipartite_signed_re_pos
    [Fintype V] [DecidableEq V]
    (A : V → Bool) (x y : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hpos : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φ).re) :
    (A x = true → A y = true → 0 < (twoSpinCorrelationS x y Φ).re) ∧
      (A x = false → A y = false → 0 < (twoSpinCorrelationS x y Φ).re) ∧
      (A x = true → A y = false → (twoSpinCorrelationS x y Φ).re < 0) ∧
      (A x = false → A y = true → (twoSpinCorrelationS x y Φ).re < 0) := by
  constructor
  · intro hx hy
    exact twoSpinCorrelationS_re_pos_of_same_of_bipartite_signed_re_pos A hpos
      (by rw [hx, hy])
  constructor
  · intro hx hy
    exact twoSpinCorrelationS_re_pos_of_same_of_bipartite_signed_re_pos A hpos
      (by rw [hx, hy])
  constructor
  · intro hx hy
    exact twoSpinCorrelationS_re_neg_of_ne_of_bipartite_signed_re_pos A hpos
      (by rw [hx, hy]; decide)
  · intro hx hy
    exact twoSpinCorrelationS_re_neg_of_ne_of_bipartite_signed_re_pos A hpos
      (by rw [hx, hy]; decide)

end LatticeSystem.Quantum
