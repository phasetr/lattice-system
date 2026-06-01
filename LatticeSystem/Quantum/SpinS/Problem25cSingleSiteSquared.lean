import LatticeSystem.Quantum.SpinS.SingleSiteCasimirExpectation

/-!
# Tasaki Problem 2.5.c: single-site squared expectation bridge

This module records the algebraic bridge for Tasaki Problem 2.5.c.  The
universal single-site Casimir identity already gives

`⟨Φ, Ŝ_x · Ŝ_x Φ⟩ = N(N+2)/4`

for normalized `Φ`, where `N = 2S`.  If a later SU(2)-symmetry input supplies
equality of the three squared Cartesian single-site expectations at `x`, then
each common value is one third of the Casimir value:

`⟨Φ, (Ŝ_x^(α))² Φ⟩ = N(N+2)/12 = S(S+1)/3`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The expectation value of the squared single-site spin operator
`(onSiteS x A)^2` in the state `Φ`. -/
noncomputable def singleSiteSpinSquareExpectationS (x : V)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ) (((onSiteS x A : ManyBodyOpS V N) * onSiteS x A).mulVec Φ)

/-- The sum of the three squared-axis single-site expectations is the
single-site Casimir expectation. -/
theorem singleSiteSpinSquareExpectationS_axis_sum (x : V)
    (Φ : (V → Fin (N + 1)) → ℂ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ +
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ +
        singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
      dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) := by
  unfold singleSiteSpinSquareExpectationS spinSDot
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add]

/-- For a normalized state, the sum of the three squared-axis single-site
expectations is `N(N+2)/4 = S(S+1)`. -/
theorem singleSiteSpinSquareExpectationS_axis_sum_normalized (x : V)
    {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : dotProduct (star Φ) Φ = 1) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ +
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ +
        singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
      (N : ℂ) * (N + 2) / 4 := by
  rw [singleSiteSpinSquareExpectationS_axis_sum, spinSDot_self_expectation_normalized x hΦ]

/-- Problem 2.5.c algebraic reduction: if the three squared-axis expectations
are equal in a normalized state, then the axis-1 value is
`N(N+2)/12 = S(S+1)/3`. -/
theorem singleSiteSpinSquareExpectationS_axis1_eq_of_axes_equal_normalized
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : dotProduct (star Φ) Φ = 1)
    (h12 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ)
    (h13 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      (N : ℂ) * (N + 2) / 12 := by
  let e1 := singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ
  let e2 := singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ
  let e3 := singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ
  have hsum : e1 + e2 + e3 = (N : ℂ) * (N + 2) / 4 :=
    singleSiteSpinSquareExpectationS_axis_sum_normalized x hΦ
  have h12e : e1 = e2 := by simpa [e1, e2] using h12
  have h13e : e1 = e3 := by simpa [e1, e3] using h13
  have hsum_eq : e1 + e1 + e1 = (N : ℂ) * (N + 2) / 4 := by
    calc
      e1 + e1 + e1 = e1 + e2 + e3 := by
        rw [← h12e, ← h13e]
      _ = (N : ℂ) * (N + 2) / 4 := hsum
  have hthree : (3 : ℂ) * e1 = (N : ℂ) * (N + 2) / 4 := by
    calc
      (3 : ℂ) * e1 = e1 + e1 + e1 := by ring
      _ = (N : ℂ) * (N + 2) / 4 := hsum_eq
  calc
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ = e1 := rfl
    _ = (1 / 3 : ℂ) * ((3 : ℂ) * e1) := by ring
    _ = (1 / 3 : ℂ) * ((N : ℂ) * (N + 2) / 4) := by rw [hthree]
    _ = (N : ℂ) * (N + 2) / 12 := by ring

/-- Problem 2.5.c algebraic reduction for all three axes, packaged as a
conjunction under the equal-axis hypotheses. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axes_equal_normalized
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : dotProduct (star Φ) Φ = 1)
    (h12 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ)
    (h13 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  have h1 := singleSiteSpinSquareExpectationS_axis1_eq_of_axes_equal_normalized
    (x := x) hΦ h12 h13
  exact ⟨h1, ⟨h12.symm.trans h1, h13.symm.trans h1⟩⟩

end LatticeSystem.Quantum
