/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

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

end LatticeSystem.Quantum
