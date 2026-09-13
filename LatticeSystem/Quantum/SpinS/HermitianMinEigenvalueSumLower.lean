import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh
import LatticeSystem.Quantum.SpinS.RayleighRitzEquality
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# Minimum-eigenvalue lower bounds for sums of Hermitian matrices

This file packages the finite-dimensional operator-order step used in
Tasaki §2.5 Problem 2.5.b.  If every local Hamiltonian has a known ground-energy
lower bound, then their sum has the sum of those lower bounds.  This is the
Rayleigh-Ritz/minimum-eigenvalue version of Tasaki's Lemma A.5 argument.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497, and Lemma A.5, p. 468.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*}

variable [Fintype n]

/-- The Rayleigh quotient is additive over finite sums of matrices. -/
theorem rayleighOnVec_sum_matrix {ι : Type*} (s : Finset ι) (M : ι → Matrix n n ℂ)
    (v : n → ℂ) :
    rayleighOnVec (∑ i ∈ s, M i) v = ∑ i ∈ s, rayleighOnVec (M i) v := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [rayleighOnVec]
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, rayleighOnVec_add_matrix, ih]

variable [DecidableEq n] [Nonempty n]

/-- **Tasaki Lemma A.5 as a minimum-eigenvalue sum lower bound**:
if each Hermitian summand `M i` has lower bound `ε i`, then the Hermitian minimum
eigenvalue of the finite sum is at least `∑ i, ε i`.

This is the abstract operator-order step used in Tasaki §2.5 Problem 2.5.b before
specialising the summands to the star-cluster Hamiltonians around one sublattice. -/
theorem sum_lower_bounds_le_hermitianMinEigenvalue_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix n n ℂ) (ε : ι → ℝ)
    (hM : ∀ i ∈ s, (M i).IsHermitian)
    (hε : ∀ i (hi : i ∈ s), ε i ≤ hermitianMinEigenvalue (hM i hi)) :
    ∑ i ∈ s, ε i ≤ hermitianMinEigenvalue (Matrix.isHermitian_sum s hM) := by
  classical
  obtain ⟨v, hunit, hv⟩ :=
    exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue (Matrix.isHermitian_sum s hM)
  have hterm : ∀ i ∈ s, ε i ≤ rayleighOnVec (M i) v := by
    intro i hi
    exact le_trans (hε i hi) (hermitianMinEigenvalue_le_rayleighOnVec_of_unit (hM i hi) hunit)
  calc
    ∑ i ∈ s, ε i ≤ ∑ i ∈ s, rayleighOnVec (M i) v := Finset.sum_le_sum hterm
    _ = rayleighOnVec (∑ i ∈ s, M i) v := (rayleighOnVec_sum_matrix s M v).symm
    _ = hermitianMinEigenvalue (Matrix.isHermitian_sum s hM) := hv

end LatticeSystem.Quantum
