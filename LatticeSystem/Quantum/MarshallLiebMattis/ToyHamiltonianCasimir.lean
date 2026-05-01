/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian
import LatticeSystem.Quantum.TotalSpin.Casimir

/-!
# Toy Hamiltonian as a cross-sublattice spin dot product

The MLM toy Hamiltonian (Tasaki §2.5 eq. (2.5.10), without the
`1/|Λ|` factor)

  `Ĥ_toy = Σ_{(x, y) bipartite} Ŝ_x · Ŝ_y`

decomposes through the cross-sublattice spin dot product as

  `Ĥ_toy = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`,

since the bipartite bond sum splits into the two oriented
cross-sublattice contributions. This is the bridge from the bond
sum to the operator-level Casimir form (assembled in subsequent PRs).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The cross-sublattice spin dot product is symmetric across the
bipartition: `Ŝ_A · Ŝ_¬A = Ŝ_¬A · Ŝ_A`. Each axis pair commutes by
the cross-sublattice commutativity lemmas. -/
theorem sublatticeSpinDot_complement_comm (A : Λ → Bool) :
    sublatticeSpinDot A (fun x => ! A x) =
      sublatticeSpinDot (fun x => ! A x) A := by
  unfold sublatticeSpinDot
  congr 1
  · congr 1
    · exact (sublatticeSpinHalfOp1_cross_commute A).eq
    · exact (sublatticeSpinHalfOp2_cross_commute A).eq
  · exact (sublatticeSpinHalfOp3_cross_commute A).eq

/-- The MLM toy Hamiltonian decomposes as an oriented cross-sublattice
spin dot product:
`Ĥ_toy = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`. -/
theorem heisenbergToyHamiltonian_eq_sublatticeSpinDot_sum (A : Λ → Bool) :
    heisenbergToyHamiltonian A =
      sublatticeSpinDot A (fun x => ! A x) +
        sublatticeSpinDot (fun x => ! A x) A := by
  unfold heisenbergToyHamiltonian heisenbergHamiltonian bipartiteCoupling
  rw [sublatticeSpinDot_eq_sum_sum, sublatticeSpinDot_eq_sum_sum,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · -- A x = true, A y = true: same sublattice, no contribution.
      have hne : ¬ A x ≠ A y := fun h => h (hAx.trans hAy.symm)
      rw [if_neg hne, zero_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨_, h2⟩; rw [show (fun z : Λ => ! A z) y = false from by simp [hAy]] at h2
        exact Bool.noConfusion h2
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨h1, _⟩; rw [show (fun z : Λ => ! A z) x = false from by simp [hAx]] at h1
        exact Bool.noConfusion h1
      rw [if_neg h1, if_neg h2, add_zero]
    · -- A x = true, A y = false: contributes from `Ŝ_A · Ŝ_¬A`.
      have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      have hne : A x ≠ A y := by rw [hAx, hAy']; decide
      rw [if_pos hne, one_smul]
      have h1 : A x ∧ (fun z : Λ => ! A z) y := by
        refine ⟨hAx, ?_⟩
        rw [show (fun z : Λ => ! A z) y = true from by simp [hAy']]
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨_, h⟩; rw [hAy'] at h; exact Bool.noConfusion h
      rw [if_pos h1, if_neg h2, add_zero]
  · -- A x = false branch.
    have hAx' : A x = false := by
      cases h : A x
      · rfl
      · exact absurd h hAx
    by_cases hAy : A y = true
    · -- A x = false, A y = true.
      have hne : A x ≠ A y := by rw [hAx', hAy]; decide
      rw [if_pos hne, one_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨h, _⟩; rw [hAx'] at h; exact Bool.noConfusion h
      have h2 : (fun z : Λ => ! A z) x ∧ A y := by
        refine ⟨?_, hAy⟩
        rw [show (fun z : Λ => ! A z) x = true from by simp [hAx']]
      rw [if_neg h1, if_pos h2, zero_add]
    · -- A x = false, A y = false: same sublattice, no contribution.
      have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      have hne : ¬ A x ≠ A y := fun h => h (hAx'.trans hAy'.symm)
      rw [if_neg hne, zero_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨h, _⟩; rw [hAx'] at h; exact Bool.noConfusion h
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨_, h⟩; rw [hAy'] at h; exact Bool.noConfusion h
      rw [if_neg h1, if_neg h2, add_zero]

/-- The MLM toy Hamiltonian equals twice the cross-sublattice
spin dot product:
`Ĥ_toy = 2 • Ŝ_A · Ŝ_¬A`. Combines the oriented sum form
`Ĥ_toy = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A` with the cross-sublattice
symmetry. -/
theorem heisenbergToyHamiltonian_eq_two_sublatticeSpinDot (A : Λ → Bool) :
    heisenbergToyHamiltonian A =
      (2 : ℂ) • sublatticeSpinDot A (fun x => ! A x) := by
  rw [heisenbergToyHamiltonian_eq_sublatticeSpinDot_sum]
  rw [← sublatticeSpinDot_complement_comm]
  rw [two_smul]

/-! ## Casimir identity for the total spin -/

/-- Helper: for commuting operators, `(a + b)(a + b) = a*a + 2•(a*b) + b*b`. -/
private lemma square_add_of_commute
    {a b : ManyBodyOp Λ} (h : Commute a b) :
    (a + b) * (a + b) = a * a + (2 : ℂ) • (a * b) + b * b := by
  rw [add_mul, mul_add, mul_add, h.eq, two_smul]
  abel

/-- **Casimir identity** (Tasaki §2.5 (2.5.11)): the total spin
squared decomposes across the bipartition as

`(Ŝ_tot)² = (Ŝ_A)² + 2 • (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²`.

Each axis contributes `(Ŝ_A^α + Ŝ_¬A^α)² = (Ŝ_A^α)² + 2 Ŝ_A^α Ŝ_¬A^α + (Ŝ_¬A^α)²`
by the cross-sublattice commutativity (PRs α-6g + α-6h); summing
gives the operator identity. -/
theorem totalSpinHalfSquared_eq_sublattice_casimir (A : Λ → Bool) :
    totalSpinHalfSquared Λ =
      sublatticeSpinHalfSquared A
      + (2 : ℂ) • sublatticeSpinDot A (fun x => ! A x)
      + sublatticeSpinHalfSquared (fun x => ! A x) := by
  unfold totalSpinHalfSquared sublatticeSpinHalfSquared
  rw [sublatticeSpinDot_def]
  rw [totalSpinHalfOp1_eq_sublattice_sum A,
      totalSpinHalfOp2_eq_sublattice_sum A,
      totalSpinHalfOp3_eq_sublattice_sum A]
  rw [square_add_of_commute (sublatticeSpinHalfOp1_cross_commute A),
      square_add_of_commute (sublatticeSpinHalfOp2_cross_commute A),
      square_add_of_commute (sublatticeSpinHalfOp3_cross_commute A)]
  rw [smul_add, smul_add]
  abel

/-- **Tasaki §2.5 (2.5.11) closed form** (without the `1/|Λ|` factor):
the toy Hamiltonian equals the difference of the total Casimir and
the two sublattice Casimirs:

`Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`. -/
theorem heisenbergToyHamiltonian_eq_casimir_diff (A : Λ → Bool) :
    heisenbergToyHamiltonian A =
      totalSpinHalfSquared Λ
        - sublatticeSpinHalfSquared A
        - sublatticeSpinHalfSquared (fun x => ! A x) := by
  rw [totalSpinHalfSquared_eq_sublattice_casimir A,
      heisenbergToyHamiltonian_eq_two_sublatticeSpinDot A]
  abel

/-! ## Commutativity with the total Casimir -/

/-- The toy Hamiltonian commutes with the total spin Casimir:
`Commute Ĥ_toy (Ŝ_tot)²`.  Follows from the general SU(2)
invariance of any Heisenberg-type Hamiltonian
(`heisenbergHamiltonian_commute_totalSpinHalfSquared`).

This is the standard fact used to project the toy Hamiltonian's
ground state onto a fixed `(Ŝ_tot)²` eigenspace; combined with the
Casimir identity, it underpins the `S_tot = 0` selection of the
toy ground state in Tasaki §2.5 (2.5.11)–(2.5.14). -/
theorem heisenbergToyHamiltonian_commute_totalSpinHalfSquared (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonian A) (totalSpinHalfSquared Λ) :=
  heisenbergHamiltonian_commute_totalSpinHalfSquared (bipartiteCoupling A)

/-- The toy Hamiltonian commutes with the `A`-sublattice Casimir:
`Commute Ĥ_toy (Ŝ_A)²`. Follows from the closed form
`Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` and the three pairwise
commutativities of the three Casimir operators. -/
theorem heisenbergToyHamiltonian_commute_sublatticeSpinHalfSquared (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonian A) (sublatticeSpinHalfSquared A) := by
  rw [heisenbergToyHamiltonian_eq_casimir_diff A]
  refine Commute.sub_left (Commute.sub_left ?_ ?_) ?_
  · exact (sublatticeSpinHalfSquared_commute_totalSpinHalfSquared A).symm
  · exact Commute.refl _
  · exact (sublatticeSpinHalfSquared_cross_commute A).symm

/-- The toy Hamiltonian commutes with the `¬A`-sublattice Casimir:
`Commute Ĥ_toy (Ŝ_¬A)²`. Symmetric to the `A` case. -/
theorem heisenbergToyHamiltonian_commute_sublatticeSpinHalfSquared_complement
    (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonian A)
            (sublatticeSpinHalfSquared (fun x => ! A x)) := by
  rw [heisenbergToyHamiltonian_eq_casimir_diff A]
  refine Commute.sub_left (Commute.sub_left ?_ ?_) ?_
  · exact (sublatticeSpinHalfSquared_commute_totalSpinHalfSquared
      (fun x => ! A x)).symm
  · exact sublatticeSpinHalfSquared_cross_commute A
  · exact Commute.refl _

end LatticeSystem.Quantum
