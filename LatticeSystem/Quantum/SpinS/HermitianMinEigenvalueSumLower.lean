import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh
import LatticeSystem.Quantum.SpinS.RayleighRitzEquality
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianEnergy
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

/-- Binary convenience form of `sum_lower_bounds_le_hermitianMinEigenvalue_sum`. -/
theorem add_lower_bounds_le_hermitianMinEigenvalue_add
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {a b : ℝ}
    (ha : a ≤ hermitianMinEigenvalue hA) (hb : b ≤ hermitianMinEigenvalue hB) :
    a + b ≤ hermitianMinEigenvalue (hA.add hB) := by
  obtain ⟨v, hunit, hv⟩ :=
    exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue (hA.add hB)
  have hA_le : a ≤ rayleighOnVec A v :=
    le_trans ha (hermitianMinEigenvalue_le_rayleighOnVec_of_unit hA hunit)
  have hB_le : b ≤ rayleighOnVec B v :=
    le_trans hb (hermitianMinEigenvalue_le_rayleighOnVec_of_unit hB hunit)
  calc
    a + b ≤ rayleighOnVec A v + rayleighOnVec B v := add_le_add hA_le hB_le
    _ = rayleighOnVec (A + B) v := (rayleighOnVec_add_matrix A B v).symm
    _ = hermitianMinEigenvalue (hA.add hB) := hv

/-- **Problem 2.5.b local-cluster lower-bound bridge**:
if a finite family of local Hamiltonians has the single-cluster ground energies from
Problem 2.5.a, then the minimum eigenvalue of their sum is bounded below by the sum
of those local cluster energies.

For a bipartite Heisenberg model this is the abstract form of Tasaki's decomposition
`H = ∑_{x∈A} h_x`, where each `h_x` is the star Hamiltonian centred at `x` with
`degree x` neighbours. -/
theorem tasaki25b_local_cluster_sum_lower_bound {ι : Type*} (s : Finset ι)
    (localH : ι → Matrix n n ℂ) (degree : ι → ℕ) (N : ℕ)
    (hH : ∀ x ∈ s, (localH x).IsHermitian)
    (hlocal : ∀ x (hx : x ∈ s),
      hermitianMinEigenvalue (hH x hx) = (singleClusterGSEnergyS (degree x) N).re) :
    ∑ x ∈ s, (singleClusterGSEnergyS (degree x) N).re ≤
      hermitianMinEigenvalue (Matrix.isHermitian_sum s hH) := by
  refine sum_lower_bounds_le_hermitianMinEigenvalue_sum s localH
    (fun x => (singleClusterGSEnergyS (degree x) N).re) hH ?_
  intro x hx
  rw [hlocal x hx]

/-- **Problem 2.5.b closed-form local-cluster lower bound**:
same as `tasaki25b_local_cluster_sum_lower_bound`, but with
`Re(singleClusterGSEnergyS z N)` expanded as
`-(N/2) * (zN/2 + 1)`.

This is the formal version of Tasaki's solution
`E_GS ≥ -∑_{x∈A} S(1 + |N(x)|S)` with `S = N/2`. -/
theorem tasaki25b_local_cluster_sum_lower_bound_closed_form {ι : Type*} (s : Finset ι)
    (localH : ι → Matrix n n ℂ) (degree : ι → ℕ) (N : ℕ)
    (hH : ∀ x ∈ s, (localH x).IsHermitian)
    (hlocal : ∀ x (hx : x ∈ s),
      hermitianMinEigenvalue (hH x hx) = (singleClusterGSEnergyS (degree x) N).re) :
    ∑ x ∈ s, -((N : ℝ) / 2) * ((degree x : ℝ) * (N : ℝ) / 2 + 1) ≤
      hermitianMinEigenvalue (Matrix.isHermitian_sum s hH) := by
  simpa [singleClusterGSEnergyS_re_eq] using
    tasaki25b_local_cluster_sum_lower_bound s localH degree N hH hlocal

end LatticeSystem.Quantum
