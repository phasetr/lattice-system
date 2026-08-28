import LatticeSystem.Lattice.GraphLaplacianQuadraticForm

/-!
# Test coverage for Tasaki Problem 2.4.d — the graph-Laplacian quadratic form

Fixtures for the capstone `tasaki_problem_2_4_d_graph_quadratic_form` (Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Problem 2.4.d, p. 35, solution (S.20), p. 497): given a
finite graph `(Λ, B)` and the lattice Laplacian `Δ = A - D` of eq. (2.4.13),
`Σ_{x,y} conj(g_x) Δ_{x,y} g_y = -Σ_{{x,y}∈B} |g_x - g_y|²` for arbitrary `g : Λ → ℂ`.

The concrete fixtures come in pairs, one for each side of (2.4.14), and **neither member of a pair
uses the capstone**: each side is evaluated from `latticeLaplacian_apply` and the explicit edge
set of the graph. Only when both members close does the numeric value pin the capstone, so a sign
flip on `Δ` or a mis-placed factor of `2` in the ordered-pair/bond bookkeeping makes exactly one
member of the pair fail rather than being absorbed by the capstone itself.

The degrees and edge sets of `pathGraph 2` / `pathGraph 3` are computed from
`SimpleGraph.degree_eq_sum_if_adj` and `SimpleGraph.pathGraph_adj`; a bare `decide` cannot be used
because `edgeFinset` and `neighborFinset` reduce through `Set.toFinset` and the tactic-proved
`DecidableRel (pathGraph n).Adj` instance, where kernel reduction stalls on `Eq.rec`.
-/

namespace LatticeSystem.Tests.Problem24dGraphLaplacian

open LatticeSystem.Lattice

/-! ## Concrete degrees and edge sets -/

/-- Every vertex of `pathGraph 2` has degree `1`. -/
private lemma pathGraph_two_degree (x : Fin 2) :
    (((SimpleGraph.pathGraph 2).degree x : ℕ) : ℂ) = 1 := by
  rw [SimpleGraph.degree_eq_sum_if_adj (SimpleGraph.pathGraph 2) (R := ℂ) x,
    Fin.sum_univ_two]
  fin_cases x <;> simp [SimpleGraph.pathGraph_adj]

/-- The middle vertex of `pathGraph 3` has degree `2`; this is the entry that makes the
three-vertex fixtures discriminate the ordered-pair/bond factor of `2`. -/
private lemma pathGraph_three_degree_middle :
    (((SimpleGraph.pathGraph 3).degree 1 : ℕ) : ℂ) = 2 := by
  rw [SimpleGraph.degree_eq_sum_if_adj (SimpleGraph.pathGraph 3) (R := ℂ) 1,
    Fin.sum_univ_three]
  norm_num [SimpleGraph.pathGraph_adj]

/-- `pathGraph 2` has the single bond `{0, 1}`. -/
private lemma pathGraph_two_edgeFinset :
    (SimpleGraph.pathGraph 2).edgeFinset = {s(0, 1)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.pathGraph_adj, Finset.mem_singleton, Sym2.eq_iff]
    revert x y
    decide

/-- `pathGraph 3` has exactly the two bonds `{0, 1}` and `{1, 2}`. -/
private lemma pathGraph_three_edgeFinset :
    (SimpleGraph.pathGraph 3).edgeFinset = {s(0, 1), s(1, 2)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.pathGraph_adj, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    revert x y
    decide

/-! ## Capstone signature pin -/

/-- **Capstone signature pin.** The Problem 2.4.d capstone
(`tasaki_problem_2_4_d_graph_quadratic_form`) takes exactly `[Fintype Λ] [DecidableEq Λ]
(G : SimpleGraph Λ) [DecidableRel G.Adj] (g : Λ → ℂ)` — no `Nonempty`, no connectivity, no
hypothesis on `g` (the identity is unconditional). This fixture is fail-closed against a
later-added hypothesis: adding one to the capstone's own signature (not this fixture's) breaks the
match. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (g : Λ → ℂ) :
    ∑ x : Λ, ∑ y : Λ, (starRingEnd ℂ) (g x) * latticeLaplacian G x y * g y
      = -∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun x y => ((Complex.normSq (g x - g y) : ℝ) : ℂ),
            fun a b => by
              change ((Complex.normSq (g a - g b) : ℝ) : ℂ)
                = ((Complex.normSq (g b - g a) : ℝ) : ℂ)
              rw [← Complex.normSq_neg (g a - g b), neg_sub]⟩ e :=
  tasaki_problem_2_4_d_graph_quadratic_form G g

/-! ## Sign fixture, 2-vertex single-edge graph -/

/-- **Sign fixture, left-hand side.** For `G = pathGraph 2` and `g = ![a, b]` the quadratic form of
`Δ` evaluates, straight from `latticeLaplacian_apply`, to `-|a - b|²`. A flipped Laplacian sign
(`Δ = D - A` instead of Tasaki's `Δ = A - D`) turns this into `+|a - b|²` and the fixture fails. -/
example (a b : ℂ) :
    ∑ x : Fin 2, ∑ y : Fin 2,
        (starRingEnd ℂ) (![a, b] x) * latticeLaplacian (SimpleGraph.pathGraph 2) x y * ![a, b] y
      = -((Complex.normSq (a - b) : ℝ) : ℂ) := by
  have h00 : latticeLaplacian (SimpleGraph.pathGraph 2) 0 0 = -1 := by
    rw [latticeLaplacian_apply, if_pos rfl, pathGraph_two_degree]
  have h11 : latticeLaplacian (SimpleGraph.pathGraph 2) 1 1 = -1 := by
    rw [latticeLaplacian_apply, if_pos rfl, pathGraph_two_degree]
  have h01 : latticeLaplacian (SimpleGraph.pathGraph 2) 0 1 = 1 := by
    rw [latticeLaplacian_apply, if_neg (by decide : ¬ (0 : Fin 2) = 1),
      if_pos (SimpleGraph.pathGraph_adj.mpr (Or.inl (by decide)))]
  have h10 : latticeLaplacian (SimpleGraph.pathGraph 2) 1 0 = 1 := by
    rw [latticeLaplacian_apply, if_neg (by decide : ¬ (1 : Fin 2) = 0),
      if_pos (SimpleGraph.pathGraph_adj.mpr (Or.inr (by decide)))]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, h00, h01, h10, h11]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.mul_conj, map_sub]
  ring

/-- **Sign fixture, right-hand side.** The capstone's bond sum for `G = pathGraph 2`,
`g = ![a, b]`, evaluated from the explicit edge set `{s(0, 1)}`, is also `-|a - b|²`. Together with
the previous fixture this pins (2.4.14) at the smallest graph with an edge, without invoking the
capstone. -/
example (a b : ℂ) :
    -∑ e ∈ (SimpleGraph.pathGraph 2).edgeFinset,
        Sym2.lift ⟨fun x y => ((Complex.normSq (![a, b] x - ![a, b] y) : ℝ) : ℂ),
          fun p q => by
            change ((Complex.normSq (![a, b] p - ![a, b] q) : ℝ) : ℂ)
              = ((Complex.normSq (![a, b] q - ![a, b] p) : ℝ) : ℂ)
            rw [← Complex.normSq_neg (![a, b] p - ![a, b] q), neg_sub]⟩ e
      = -((Complex.normSq (a - b) : ℝ) : ℂ) := by
  rw [pathGraph_two_edgeFinset, Finset.sum_singleton, Sym2.lift_mk]
  norm_num

/-! ## Factor-of-2 / degree-bookkeeping fixture, 3-vertex path graph -/

/-- **Factor-of-2 fixture, left-hand side.** For `G = pathGraph 3` and `g = ![0, 1, 0]` only the
middle vertex contributes, through its degree `2`, so the quadratic form is `-2`. Dropping the
degree factor would give `-1`. -/
example :
    ∑ x : Fin 3, ∑ y : Fin 3,
        (starRingEnd ℂ) (![(0 : ℂ), 1, 0] x) * latticeLaplacian (SimpleGraph.pathGraph 3) x y
          * ![(0 : ℂ), 1, 0] y
      = (-2 : ℂ) := by
  have h11 : latticeLaplacian (SimpleGraph.pathGraph 3) 1 1 = -2 := by
    rw [latticeLaplacian_apply, if_pos rfl, pathGraph_three_degree_middle]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, h11]
  simp

/-- **Factor-of-2 fixture, right-hand side.** The capstone's bond sum over the two bonds of
`pathGraph 3` contributes `|0 - 1|² + |1 - 0|² = 2`, hence `-2`. This is the discriminating case
for the ordered-pair-sum-vs-bond-sum bookkeeping: summing ordered pairs without the bond
correction would give `-4`, and halving the correct bond sum would give `-1`. What the 2-vertex
fixtures cannot see is the degree-coefficient mode of the left-hand fixture above: every vertex of
`pathGraph 2` has degree `1`, so replacing the diagonal `-|N(x)|` by a constant `-1` leaves both
2-vertex fixtures unchanged. -/
example :
    -∑ e ∈ (SimpleGraph.pathGraph 3).edgeFinset,
        Sym2.lift ⟨fun x y => ((Complex.normSq (![(0 : ℂ), 1, 0] x - ![(0 : ℂ), 1, 0] y) : ℝ) : ℂ),
          fun p q => by
            change ((Complex.normSq (![(0 : ℂ), 1, 0] p - ![(0 : ℂ), 1, 0] q) : ℝ) : ℂ)
              = ((Complex.normSq (![(0 : ℂ), 1, 0] q - ![(0 : ℂ), 1, 0] p) : ℝ) : ℂ)
            rw [← Complex.normSq_neg (![(0 : ℂ), 1, 0] p - ![(0 : ℂ), 1, 0] q), neg_sub]⟩ e
      = (-2 : ℂ) := by
  rw [pathGraph_three_edgeFinset, Finset.sum_insert (by simp), Finset.sum_singleton,
    Sym2.lift_mk, Sym2.lift_mk]
  simp
  norm_num

/-! ## Constant `g` -/

/-- **Constant-`g` vanishing.** On an arbitrary finite graph a constant `g` makes every bond term
`|g_x - g_y|²` vanish, so the capstone forces the quadratic form of `Δ` to be `0`. This is the
fixture that would fail if the capstone's right-hand side carried a spurious diagonal
(degree-weighted) contribution surviving at constant `g`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (c : ℂ) :
    ∑ x : Λ, ∑ y : Λ,
        (starRingEnd ℂ) ((fun _ : Λ => c) x) * latticeLaplacian G x y * (fun _ : Λ => c) y = 0 := by
  rw [tasaki_problem_2_4_d_graph_quadratic_form G (fun _ => c), neg_eq_zero]
  refine Finset.sum_eq_zero fun e he => ?_
  clear he
  induction e using Sym2.ind with
  | _ x y => simp

end LatticeSystem.Tests.Problem24dGraphLaplacian
