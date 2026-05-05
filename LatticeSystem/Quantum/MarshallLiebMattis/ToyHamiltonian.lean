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

/-- **Total ordered pair count** on a bipartite split:
`Σ_{x, y} bipartiteCoupling A x y = 2 · |A| · |¬A|`.

Each cross-sublattice ordered pair contributes `1`; same-sublattice pairs
(including the diagonal `x = y`) contribute `0`. The factor `2` reflects
that each unordered cross pair `{a, b}` is counted twice as `(a, b)` and
`(b, a)`. -/
theorem bipartiteCoupling_sum (A : Λ → Bool) :
    ∑ x : Λ, ∑ y : Λ, bipartiteCoupling A x y =
      2 * ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
  classical
  unfold bipartiteCoupling
  have h_inner : ∀ x : Λ,
      (∑ y : Λ, (if A x ≠ A y then (1 : ℂ) else 0)) =
      (if A x = true
       then ((Finset.univ.filter (fun y : Λ => (! A y) = true)).card : ℂ)
       else ((Finset.univ.filter (fun y : Λ => A y = true)).card : ℂ)) := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      have heq : ∀ y : Λ, A x ≠ A y ↔ (! A y) = true := by
        intro y; rw [hAx]; cases A y <;> decide
      simp_rw [heq]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    · rw [if_neg hAx]
      have hAxF : A x = false := by
        cases h : A x with
        | true => exact absurd h hAx
        | false => rfl
      have heq : ∀ y : Λ, A x ≠ A y ↔ A y = true := by
        intro y; rw [hAxF]; cases A y <;> decide
      simp_rw [heq]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [h_inner]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
  have h_filter_eq :
      (Finset.univ.filter (fun x : Λ => ¬ (A x = true))).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    congr 1
    apply Finset.filter_congr
    intros x _
    cases A x <;> simp
  rw [h_filter_eq]
  ring

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
