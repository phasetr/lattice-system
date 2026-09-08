import LatticeSystem.Quantum.SpinS.FerromagneticHeisenbergSign

/-!
# Tasaki §2.4, p. 34: Perron-Frobenius irreducibility on a magnetization sector

The graph-theoretic half of the Theorem 2.1 uniqueness argument.  Tasaki's Theorem A.18 (p. 475)
applies to a real symmetric matrix whose off-diagonal entries are non-positive and whose indices
are all connected through non-vanishing entries.  The first condition is the ferromagnetic sign
structure; the second is property (iii) of the Proof of Theorem 2.2 (pp. 41-42): on a connected
graph any two configurations of equal magnetization are joined by a finite chain of `Ŝ⁺_x Ŝ⁻_y`
moves along edges.

This module supplies the shift `c` that turns `Ĥ` into a non-negative matrix and assembles the
two conditions into `Matrix.IsIrreducible` for `c·1 - Ĥ` restricted to a magnetization sector,
the form in which the repo's Perron-Frobenius machinery consumes them.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; Proof of Theorem 2.2, property (iii), pp. 41-42; solution of
Problem 2.4.a, p. 496; Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **A strict upper bound for the diagonal.**  The Perron-Frobenius argument is run on the
shifted matrix `c·1 - Ĥ` (Tasaki Theorem A.18, p. 475, applied to `-Ĥ` up to a shift), which
needs a `c` strictly above every diagonal entry so that the shifted diagonal is strictly
positive.  The configuration space is finite, so a bound exists and adding one makes it
strict. -/
theorem exists_gt_heisenbergHamiltonianSReMatrix_diag (J : V → V → ℂ) (N : ℕ) :
    ∃ c : ℝ, ∀ σ : V → Fin (N + 1), heisenbergHamiltonianSReMatrix J N σ σ < c := by
  obtain ⟨b, hb⟩ :=
    Finite.exists_le (fun σ : V → Fin (N + 1) => heisenbergHamiltonianSReMatrix J N σ σ)
  exact ⟨b + 1, fun σ => lt_of_le_of_lt (hb σ) (lt_add_one b)⟩

end LatticeSystem.Quantum
