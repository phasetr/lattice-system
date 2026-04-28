/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Primitivity criterion: irreducible + positive diagonal

We prove that a nonneg irreducible matrix with strictly positive diagonal entries is primitive
(Seneta, *Non-negative Matrices and Markov Chains*, §1.1, Definition 1.1 and Proposition 1.3
(pp. 14, 17); Springer 2006).

The proof uses a monotonicity argument: once `(A^m)_{ij} > 0`, the positive diagonal entry
`A_{jj} > 0` forces `(A^{m+1})_{ij} ≥ (A^m)_{ij} * A_{jj} > 0`, propagating positivity
to all higher powers.  Taking `M = max_{i,j} m_{ij}` over all pairs yields a uniform exponent
at which every entry is strictly positive.

This result is a prerequisite for the Collatz-Wielandt approach to the Perron-Frobenius theorem
(see `PerronFrobenius.lean`, Issue #405).

## Implementation note

The MCMC repository (https://github.com/or4nge19/MCMC,
`MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.lean`,
theorem `IsPrimitive.of_irreducible_pos_diagonal`) proves the same result using quiver-path
replication (appending self-loops to make paths of length `(N-1)*N+1`).  The proof here
diverges: it uses direct algebraic monotonicity and requires no custom quiver-path library,
relying only on `Matrix.pow_apply_nonneg` and `isIrreducible_iff_exists_pow_pos`.

## References
- E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.), Springer 2006,
  §1.1, Definition 1.1 (p. 14) and Proposition 1.3 (p. 17).
- MCMC Lean source: https://github.com/or4nge19/MCMC,
  `MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.lean`.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]

/-- An irreducible nonneg matrix with strictly positive diagonal entries is primitive.

**Proof**: by `isIrreducible_iff_exists_pow_pos`, every pair `(i, j)` admits some `m_{ij} ≥ 1`
with `(A^{m_{ij}})_{ij} > 0`.  The diagonal entry `A_{jj} > 0` propagates positivity:
once `(A^m)_{ij} > 0`, we have `(A^{m+t})_{ij} ≥ (A^{m+t-1})_{ij} * A_{jj} > 0`.
Setting `M = max_{i,j} m_{ij}` gives `(A^M)_{ij} > 0` for all `i, j`.

**References**: Seneta §1.1, Proposition 1.3 (p. 17); MCMC `Lemmas.lean`
`IsPrimitive.of_irreducible_pos_diagonal` (different proof strategy). -/
theorem IsPrimitive.of_irreducible_pos_diagonal
    {A : Matrix n n ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_irred : A.IsIrreducible)
    (hA_diag : ∀ i, 0 < A i i) :
    A.IsPrimitive := by
  refine ⟨hA_nonneg, ?_⟩
  -- Monotonicity: positivity at (m, i, j) propagates to (m + t, i, j) for all t.
  have mono : ∀ (i j : n) (m t : ℕ), 0 < (A ^ m) i j → 0 < (A ^ (m + t)) i j := by
    intro i j m t hm
    induction t with
    | zero => simpa
    | succ t' ih =>
      rw [show m + (t' + 1) = (m + t') + 1 from by omega, pow_succ, mul_apply]
      apply Finset.sum_pos'
      · intro k _
        exact mul_nonneg (pow_apply_nonneg hA_nonneg _ i k) (hA_nonneg k j)
      · exact ⟨j, Finset.mem_univ _, mul_pos ih (hA_diag j)⟩
  -- By irreducibility, for every pair choose a positive exponent.
  have exist_exp : ∀ i j : n, ∃ m : ℕ, 0 < m ∧ 0 < (A ^ m) i j :=
    fun i j => (isIrreducible_iff_exists_pow_pos hA_nonneg).mp hA_irred i j
  classical
  -- Noncomputably pick one exponent per pair.
  let exp : n → n → ℕ := fun i j => (exist_exp i j).choose
  have exp_pos : ∀ i j, 0 < exp i j :=
    fun i j => ((exist_exp i j).choose_spec).1
  have exp_pow : ∀ i j, 0 < (A ^ exp i j) i j :=
    fun i j => ((exist_exp i j).choose_spec).2
  -- Uniform exponent: M = max over all pairs.
  let M := Finset.univ.sup' Finset.univ_nonempty
             (fun i => Finset.univ.sup' Finset.univ_nonempty (exp i))
  refine ⟨M, ?_, ?_⟩
  · -- M > 0: any pair contributes exp ≥ 1.
    let i₀ := Classical.arbitrary n
    let j₀ := Classical.arbitrary n
    let rowSup : n → ℕ := fun i => Finset.univ.sup' Finset.univ_nonempty (exp i)
    calc 0 < exp i₀ j₀ := exp_pos i₀ j₀
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (exp i₀) :=
            Finset.le_sup' (exp i₀) (Finset.mem_univ j₀)
      _ ≤ M := Finset.le_sup' rowSup (Finset.mem_univ i₀)
  · -- All entries of A^M are positive by monotonicity.
    intro i j
    let rowSup : n → ℕ := fun i => Finset.univ.sup' Finset.univ_nonempty (exp i)
    have h_le : exp i j ≤ M :=
      (Finset.le_sup' (exp i) (Finset.mem_univ j)).trans
        (Finset.le_sup' rowSup (Finset.mem_univ i))
    have := mono i j (exp i j) (M - exp i j) (exp_pow i j)
    rwa [Nat.add_sub_cancel' h_le] at this

end Matrix
