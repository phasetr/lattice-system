import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Sublattice spin-`S` operators (Tasaki §2.5 Theorem 2.3 prep)

To establish the Casimir identity used in Tasaki Theorem 2.3
(`|A| ≠ |B|` case),

  `Ĥ_toy = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)`,

we need spin-`S` analogues of the **sublattice spin operators**
already defined for spin-`1/2`
(`Quantum/MarshallLiebMattis/SublatticeSpin.lean`):

  `Ŝ_A^(α) := Σ_{x : A x = true} onSiteS x (spinSOp_α N)`,
  `Ŝ_¬A^(α) := Σ_{x : A x = false} onSiteS x (spinSOp_α N)`.

The total spin-`S` then decomposes as
`Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_¬A^(α)`.

This module defines the spin-`S` sublattice operators and the
decomposition. First step in the γ-4 multi-PR effort tracked
under Issue #412.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.3 (p. 42), eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Sublattice spin-`S` operators -/

/-- The sublattice-`A` total spin-`S` (axis 1):
`Ŝ_A^(1) := Σ_{x : A x} onSiteS x (spinSOp1 N)`. -/
noncomputable def sublatticeSpinSOp1 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp1 N) else 0

/-- The sublattice-`A` total spin-`S` (axis 2):
`Ŝ_A^(2) := Σ_{x : A x} onSiteS x (spinSOp2 N)`. -/
noncomputable def sublatticeSpinSOp2 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp2 N) else 0

/-- The sublattice-`A` total spin-`S` (axis 3):
`Ŝ_A^(3) := Σ_{x : A x} onSiteS x (spinSOp3 N)`. -/
noncomputable def sublatticeSpinSOp3 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp3 N) else 0

/-! ## Decomposition of the total spin into sublattices -/

/-- The total spin-`S` (axis 1) decomposes as a sum over the two
sublattices: `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem totalSpinSOp1_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp1 Λ N =
      sublatticeSpinSOp1 N A + sublatticeSpinSOp1 N (fun x => ! A x) := by
  unfold totalSpinSOp1 sublatticeSpinSOp1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin-`S` (axis 2) decomposes as a sum over the two
sublattices. -/
theorem totalSpinSOp2_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp2 Λ N =
      sublatticeSpinSOp2 N A + sublatticeSpinSOp2 N (fun x => ! A x) := by
  unfold totalSpinSOp2 sublatticeSpinSOp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin-`S` (axis 3) decomposes as a sum over the two
sublattices. -/
theorem totalSpinSOp3_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp3 Λ N =
      sublatticeSpinSOp3 N A + sublatticeSpinSOp3 N (fun x => ! A x) := by
  unfold totalSpinSOp3 sublatticeSpinSOp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

end LatticeSystem.Quantum
