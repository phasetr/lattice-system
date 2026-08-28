import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The lattice Laplacian and its complex quadratic form (Tasaki Problem 2.4.d)

Red-fixture skeleton for Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Problem 2.4.d, p. 35: given a finite graph `(Λ, B)`, eq. (2.4.13) defines the lattice Laplacian
`Δ_{x,y} = -|N(x)|` if `x = y`, `1` if `{x,y} ∈ B`, `0` otherwise, and eq. (2.4.14) states
`Σ_{x,y} conj(g_x) Δ_{x,y} g_y = -Σ_{{x,y}∈B} |g_x - g_y|²` for arbitrary `g : Λ → ℂ`.

This module currently contains only `latticeLaplacian` (2.4.13), so that
`LatticeSystem/Tests/Problem24dGraphLaplacian.lean` can import a resolving module while its
signature-pin fixture for the capstone `tasaki_problem_2_4_d_graph_quadratic_form` still fails on
the *identifier* (TDD Red). The capstone (2.4.14) and its supporting lemmas are added in
follow-up commits.
-/

namespace LatticeSystem.Lattice

variable {Λ : Type*}

/-- The lattice Laplacian `Δ` of Tasaki (2.4.13), p. 35: the negative of mathlib's
`SimpleGraph.lapMatrix` (`L = D - A`), i.e. `Δ = A - D`. Entrywise, `Δ_{x,y} = -|N(x)|` if
`x = y`, `1` if `{x,y}` is an edge, `0` otherwise (see `latticeLaplacian_apply`, added later). -/
def latticeLaplacian [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ) [DecidableRel G.Adj] :
    Matrix Λ Λ ℂ :=
  -(G.lapMatrix ℂ)

end LatticeSystem.Lattice
