/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain

/-!
# Toy Hamiltonian for the Marshall–Lieb–Mattis theorem (Tasaki §2.5 p. 40)

To extend the MLM Theorem 2.2 result from `H_0` (zero magnetisation
sector) to the full Hilbert space, Tasaki §2.5 (pp. 40–41)
introduces a **toy Hamiltonian**

  `Ĥ_toy := (1/|Λ|) Σ_{x ∈ A, y ∈ B} Ŝ_x · Ŝ_y = (1/|Λ|) Ŝ_A · Ŝ_B`

on the same lattice as the AFM Heisenberg model, where `A`, `B` are
the two sublattices and `Ŝ_A := Σ_{x ∈ A} Ŝ_x`, `Ŝ_B := Σ_{y ∈ B} Ŝ_y`.
The toy Hamiltonian is a special case of the Heisenberg Hamiltonian
with bipartite coupling.

This module:

1. Defines the bipartite coupling
   `bipartiteCoupling A : Λ → Λ → ℂ := if A x ≠ A y then 1 else 0`
   (omitting the `1/|Λ|` normalisation factor, which only affects
   spectrum scaling, not eigenvectors).
2. Defines the toy Hamiltonian as
   `heisenbergToyHamiltonian A := heisenbergHamiltonian (bipartiteCoupling A)`.
3. Establishes Hermiticity, real-symmetric coupling, bipartite
   support, and non-negativity properties needed for the MLM
   application.

The Casimir identity `Ĥ_toy = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)`
and the angular-momentum-addition argument that `Ĥ_toy`'s ground
state has `(Ŝ_tot)² = 0` are deferred to subsequent PRs.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 pp. 40–41, especially eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The bipartite coupling: `J(x, y) = 1` if `(x, y)` crosses the
bipartition (`A x ≠ A y`), and `0` otherwise.

This is the (unnormalised) coupling for the MLM toy Hamiltonian
(Tasaki §2.5 eq. (2.5.10), without the `1/|Λ|` factor). -/
noncomputable def bipartiteCoupling (A : Λ → Bool) : Λ → Λ → ℂ :=
  fun x y => if A x ≠ A y then 1 else 0

/-- The bipartite coupling is real (no imaginary part). -/
theorem bipartiteCoupling_im (A : Λ → Bool) (x y : Λ) :
    (bipartiteCoupling A x y).im = 0 := by
  unfold bipartiteCoupling
  by_cases h : A x ≠ A y
  · rw [if_pos h]; simp
  · rw [if_neg h]; simp

/-- The bipartite coupling is symmetric: `J(x, y) = J(y, x)`. -/
theorem bipartiteCoupling_symm (A : Λ → Bool) (x y : Λ) :
    bipartiteCoupling A x y = bipartiteCoupling A y x := by
  unfold bipartiteCoupling
  by_cases h : A x ≠ A y
  · rw [if_pos h, if_pos (fun heq => h heq.symm)]
  · rw [if_neg h]
    push Not at h
    rw [if_neg (by push Not; exact h.symm)]

/-- The bipartite coupling is non-negative: `0 ≤ (J(x, y)).re`. -/
theorem bipartiteCoupling_nonneg (A : Λ → Bool) (x y : Λ) :
    0 ≤ (bipartiteCoupling A x y).re := by
  unfold bipartiteCoupling
  by_cases h : A x ≠ A y
  · rw [if_pos h]; simp
  · rw [if_neg h]; simp

/-- The bipartite coupling vanishes on intra-sublattice pairs:
`A x = A y → J(x, y) = 0`. -/
theorem bipartiteCoupling_eq_zero_of_same_sublattice
    (A : Λ → Bool) {x y : Λ} (h : A x = A y) :
    bipartiteCoupling A x y = 0 := by
  unfold bipartiteCoupling
  rw [if_neg]
  push Not
  exact h

/-- The bipartite coupling is positive on inter-sublattice pairs:
`A x ≠ A y → 0 < (J(x, y)).re`. -/
theorem bipartiteCoupling_pos_of_diff_sublattice
    (A : Λ → Bool) {x y : Λ} (h : A x ≠ A y) :
    0 < (bipartiteCoupling A x y).re := by
  unfold bipartiteCoupling
  rw [if_pos h]
  simp

/-! ## Toy Hamiltonian -/

/-- The **MLM toy Hamiltonian** (Tasaki §2.5 eq. (2.5.10)
without the `1/|Λ|` factor): the Heisenberg Hamiltonian with
bipartite coupling. -/
noncomputable def heisenbergToyHamiltonian (A : Λ → Bool) : ManyBodyOp Λ :=
  heisenbergHamiltonian (bipartiteCoupling A)

/-- The toy Hamiltonian is Hermitian (real symmetric coupling). -/
theorem heisenbergToyHamiltonian_isHermitian (A : Λ → Bool) :
    (heisenbergToyHamiltonian A).IsHermitian := by
  unfold heisenbergToyHamiltonian
  refine heisenbergHamiltonian_isHermitian_of_real_symm ?_ (bipartiteCoupling_symm A)
  intro x y
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
  · rw [Complex.star_def, Complex.conj_im, bipartiteCoupling_im, neg_zero]

end LatticeSystem.Quantum
