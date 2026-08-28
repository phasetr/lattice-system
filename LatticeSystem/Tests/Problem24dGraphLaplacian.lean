import LatticeSystem.Lattice.GraphLaplacianQuadraticForm
import LatticeSystem.Lattice.Graph

/-!
# Test coverage for Tasaki Problem 2.4.d — the graph-Laplacian quadratic form

Fixtures for the capstone `tasaki_problem_2_4_d_graph_quadratic_form` (Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Problem 2.4.d, p. 35, solution (S.20), p. 497): given a
finite graph `(Λ, B)` and the lattice Laplacian `Δ = A - D` of eq. (2.4.13),
`Σ_{x,y} conj(g_x) Δ_{x,y} g_y = -Σ_{{x,y}∈B} |g_x - g_y|²` for arbitrary `g : Λ → ℂ`.

**TDD status: Red.** Only `latticeLaplacian` (2.4.13) exists so far
(`LatticeSystem/Lattice/GraphLaplacianQuadraticForm.lean`); the capstone
`tasaki_problem_2_4_d_graph_quadratic_form` (2.4.14) does not exist yet, so every fixture below
fails to elaborate with `unknown identifier 'tasaki_problem_2_4_d_graph_quadratic_form'`. Each
`example`'s *type* is nonetheless already the concrete claim it will discharge once the capstone
is implemented, so the Red pins the exact statement and the exact numeric error modes it must
rule out.
-/

namespace LatticeSystem.Tests.Problem24dGraphLaplacian

open LatticeSystem.Lattice

/-! ## Capstone signature pin -/

/-- **Capstone signature pin.** The Problem 2.4.d capstone
(`tasaki_problem_2_4_d_graph_quadratic_form`) takes exactly `[Fintype Λ] [DecidableEq Λ]
(G : SimpleGraph Λ) [DecidableRel G.Adj] (g : Λ → ℂ)` — no `Nonempty`, no connectivity, no
hypothesis on `g` (the identity is unconditional, design §2 L5). This fixture is fail-closed
against a later-added hypothesis: adding one to the capstone's own signature (not this fixture's)
breaks the match. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (g : Λ → ℂ) :
    ∑ x : Λ, ∑ y : Λ, (starRingEnd ℂ) (g x) * latticeLaplacian G x y * g y
      = -∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun x y => ((Complex.normSq (g x - g y) : ℝ) : ℂ),
            fun a b => by
              show ((Complex.normSq (g a - g b) : ℝ) : ℂ)
                = ((Complex.normSq (g b - g a) : ℝ) : ℂ)
              rw [← Complex.normSq_neg (g a - g b), neg_sub]⟩ e :=
  tasaki_problem_2_4_d_graph_quadratic_form G g

/-! ## Sign fixture -/

/-- **Sign fixture, 2-vertex single-edge graph.** `G = pathGraph 2`, `g = ![a, b]`: both sides of
(2.4.14) evaluate to `-((normSq (a - b) : ℝ) : ℂ)`. This is the smallest instance with a
nontrivial edge, so a flipped Laplacian sign (`Δ = D - A` instead of Tasaki's `Δ = A - D`) would
force the LHS to `+((normSq (a - b) : ℝ) : ℂ)` and this fixture would fail — no other fixture in
this file is needed to catch a sign error, since the identity is already nontrivial here. -/
example (a b : ℂ) :
    ∑ x : Fin 2, ∑ y : Fin 2,
        (starRingEnd ℂ) (![a, b] x) * latticeLaplacian (SimpleGraph.pathGraph 2) x y * ![a, b] y
      = -((Complex.normSq (a - b) : ℝ) : ℂ) :=
  tasaki_problem_2_4_d_graph_quadratic_form (SimpleGraph.pathGraph 2) ![a, b]

/-! ## Factor-of-2 / degree-bookkeeping fixture -/

/-- **Factor-of-2 fixture, 3-vertex path graph.** `G = pathGraph 3`, `g = ![0, 1, 0]`: both sides
of (2.4.14) evaluate to `-2`. This is the discriminating case for the ordered-pair-sum-vs-bond-sum
bookkeeping (design §3): the middle vertex has degree `2`, so dropping its degree factor would
give `-1`, a spurious extra factor of `2` on the edge sum (summing ordered pairs without halving)
would give `-4`, and an erroneous division by `2` on top of the correct ordered-pair sum would
give `-1`; only the exact bookkeeping of L0b/L4 gives `-2`. The 2-vertex fixture above cannot
catch this mode, since it has only one edge and a degree-`1` endpoint. -/
example :
    ∑ x : Fin 3, ∑ y : Fin 3,
        (starRingEnd ℂ) (![(0 : ℂ), 1, 0] x) * latticeLaplacian (SimpleGraph.pathGraph 3) x y
          * ![(0 : ℂ), 1, 0] y
      = (-2 : ℂ) :=
  tasaki_problem_2_4_d_graph_quadratic_form (SimpleGraph.pathGraph 3) ![(0 : ℂ), 1, 0]

end LatticeSystem.Tests.Problem24dGraphLaplacian
