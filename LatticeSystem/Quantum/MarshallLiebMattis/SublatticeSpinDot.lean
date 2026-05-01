/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin
import LatticeSystem.Quantum.SpinDot

/-!
# Cross-sublattice spin dot product `Ŝ_A · Ŝ_B`

To express the MLM toy Hamiltonian (Tasaki §2.5 eq. (2.5.10)–(2.5.11))
through the Casimir identity, we introduce the **cross-sublattice
spin dot product**:

  `Ŝ_A · Ŝ_B := Σ_{α=1,2,3} Ŝ_A^(α) Ŝ_B^(α)`,

where `A, B : Λ → Bool` are sublattice indicators. The key structural
fact is the bilinear expansion

  `Ŝ_A · Ŝ_B = Σ_{x : A x = true} Σ_{y : B y = true} Ŝ_x · Ŝ_y`,

which connects the operator-level Casimir form to the bond-level
Heisenberg expression used in the toy Hamiltonian.

This module:

1. Defines `sublatticeSpinDot A B`.
2. Proves the bilinear expansion to `Σ_{x ∈ A, y ∈ B} spinHalfDot x y`
   (formulated as `∑ x, ∑ y, if A x ∧ B y then spinHalfDot x y else 0`).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Cross-sublattice spin dot product -/

/-- The cross-sublattice spin dot product:
`Ŝ_A · Ŝ_B := Σ_α Ŝ_A^(α) Ŝ_B^(α)`. -/
noncomputable def sublatticeSpinDot (A B : Λ → Bool) : ManyBodyOp Λ :=
  sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B +
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 B

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^(α) Ŝ_B^(α)` is the explicit definition. -/
@[simp] theorem sublatticeSpinDot_def (A B : Λ → Bool) :
    sublatticeSpinDot A B =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 B := rfl

/-! ## Bilinear expansion -/

/-- Per-axis expansion: a single product
`Ŝ_A^(α) Ŝ_B^(α)` factors as a double sum
`Σ_x Σ_y (if A x ∧ B y then onSite x σ_α * onSite y σ_α else 0)`.

This is the bridge from the sublattice-operator product form to the
site-pair form used in the Heisenberg Hamiltonian. -/
private theorem sublatticeSpinHalfOp_mul_eq_sum_sum
    (A B : Λ → Bool) (S : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ x : Λ, if A x then onSite x S else 0) *
        (∑ y : Λ, if B y then onSite y S else 0) =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then onSite x S * onSite y S else 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hBy : B y = true
    · rw [if_pos hAx, if_pos hBy, if_pos ⟨hAx, hBy⟩]
    · rw [if_pos hAx, if_neg hBy, mul_zero, if_neg]
      rintro ⟨_, h⟩; exact hBy h
  · rw [if_neg hAx, zero_mul, if_neg]
    rintro ⟨h, _⟩; exact hAx h

/-- The cross-sublattice spin dot product expands as a double sum
over sites of the spin-dot products:
`Ŝ_A · Ŝ_B = Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`.

This is formulated using `if A x ∧ B y then ... else 0` so that the
sums are over all of `Λ`. -/
theorem sublatticeSpinDot_eq_sum_sum (A B : Λ → Bool) :
    sublatticeSpinDot A B =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then spinHalfDot x y else 0 := by
  unfold sublatticeSpinDot sublatticeSpinHalfOp1
    sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  rw [sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp1,
      sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp2,
      sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp3]
  -- Combine the three axis sums into a single sum of `spinHalfDot`.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAB : A x ∧ B y
  · simp only [if_pos hAB]
    unfold spinHalfDot
    rfl
  · simp only [if_neg hAB, add_zero]

end LatticeSystem.Quantum
