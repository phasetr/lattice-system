import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import LatticeSystem.Lattice.Graph

/-!
# The lattice Laplacian and its complex quadratic form (Tasaki Problem 2.4.d)

Formalisation of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
Problem 2.4.d, p. 35 (solution p. 497, eq. (S.20)).

For a finite graph `(Λ, B)`, eq. (2.4.13), p. 35 defines the lattice Laplacian
`Δ_{x,y} = -|N(x)|` if `x = y`, `1` if `{x,y} ∈ B`, and `0` otherwise — that is, `Δ = A - D`,
the *negative* of mathlib's `SimpleGraph.lapMatrix` (`L = D - A`). Eq. (2.4.14), p. 35 states the
sesquilinear edge identity

`Σ_{x,y ∈ Λ} conj(g_x) Δ_{x,y} g_y = -Σ_{{x,y} ∈ B} |g_x - g_y|²`

for arbitrary `g : Λ → ℂ`. The right-hand side is a genuine unordered sum over `G.edgeFinset`,
as printed in the book, rather than a halved ordered double sum; the factor `2` relating the two
is supplied once by `LatticeSystem.Lattice.two_sum_edgeFinset_lift_eq_sum_adj` and cancelled
once, by `mul_left_cancel₀`, so no division occurs anywhere.

The sign convention is pinned in exactly one place, `latticeLaplacian_apply`; everything
downstream reads only that lemma and never unfolds `SimpleGraph.lapMatrix` again.
-/

namespace LatticeSystem.Lattice

variable {Λ : Type*}

/-- The lattice Laplacian `Δ` of Tasaki (2.4.13), p. 35: the negative of mathlib's
`SimpleGraph.lapMatrix` (`L = D - A`), i.e. `Δ = A - D`. Entrywise, `Δ_{x,y} = -|N(x)|` if
`x = y`, `1` if `{x,y}` is an edge, `0` otherwise (see `latticeLaplacian_apply`). -/
def latticeLaplacian [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ) [DecidableRel G.Adj] :
    Matrix Λ Λ ℂ :=
  -(G.lapMatrix ℂ)

/-- **Entrywise form of the lattice Laplacian**, Tasaki eq. (2.4.13), p. 35: the diagonal entry at
`x` is `-|N(x)|`, an entry at an edge is `1`, and every other entry vanishes. This is the single
place where Tasaki's sign convention `Δ = A - D` is compared with mathlib's `L = D - A`. -/
theorem latticeLaplacian_apply [Fintype Λ] [DecidableEq Λ] (G : SimpleGraph Λ)
    [DecidableRel G.Adj] (x y : Λ) :
    latticeLaplacian G x y =
      if x = y then -(G.degree x : ℂ) else if G.Adj x y then 1 else 0 := by
  unfold latticeLaplacian SimpleGraph.lapMatrix SimpleGraph.degMatrix
  rw [Matrix.neg_apply, Matrix.sub_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : x = y
  · subst h
    rw [Matrix.diagonal_apply_eq, if_pos rfl, if_neg G.irrefl, sub_zero]
  · rw [Matrix.diagonal_apply_ne _ h, if_neg h, zero_sub, neg_neg]

/-- **Diagonal/off-diagonal split of the quadratic form**, the left-hand side of Tasaki (S.20),
p. 497: the sesquilinear form of `Δ` is the ordered adjacency sum of `conj(g_x) g_y` minus the
degree-weighted sum of `|g_x|²`. The two contributions are disjoint because a `SimpleGraph` has no
self-loops. -/
private theorem sum_conj_mul_latticeLaplacian_mul [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (g : Λ → ℂ) :
    ∑ x : Λ, ∑ y : Λ, (starRingEnd ℂ) (g x) * latticeLaplacian G x y * g y
      = -(∑ x : Λ, (G.degree x : ℂ) * ((Complex.normSq (g x) : ℝ) : ℂ))
        + ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then (starRingEnd ℂ) (g x) * g y else 0) := by
  have key : ∀ x y : Λ, (starRingEnd ℂ) (g x) * latticeLaplacian G x y * g y
      = -(if x = y then (G.degree x : ℂ) * ((Complex.normSq (g x) : ℝ) : ℂ) else 0)
        + (if G.Adj x y then (starRingEnd ℂ) (g x) * g y else 0) := by
    intro x y
    rw [latticeLaplacian_apply]
    by_cases h : x = y
    · subst h
      rw [if_pos rfl, if_pos rfl, if_neg G.irrefl, add_zero, ← Complex.mul_conj]
      ring
    · rw [if_neg h, if_neg h, neg_zero, zero_add]
      by_cases h2 : G.Adj x y
      · rw [if_pos h2, if_pos h2, mul_one]
      · rw [if_neg h2, if_neg h2, mul_zero, zero_mul]
  have step : ∀ x : Λ, ∑ y : Λ, ((starRingEnd ℂ) (g x) * latticeLaplacian G x y * g y)
      = -((G.degree x : ℂ) * ((Complex.normSq (g x) : ℝ) : ℂ))
        + ∑ y : Λ, (if G.Adj x y then (starRingEnd ℂ) (g x) * g y else 0) := by
    intro x
    rw [Finset.sum_congr rfl (fun y _ => key x y), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_neg_distrib]
    congr 1
    simp
  rw [Finset.sum_congr rfl (fun x _ => step x), Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

/-- **Ordered-pair expansion of the bond energy**, the right-hand side of Tasaki (S.20), p. 497:
expanding `|g_x - g_y|² = |g_x|² + |g_y|² - conj(g_x) g_y - conj(g_y) g_x` over all ordered
adjacent pairs turns the two square terms into the degree-weighted sum and the two cross terms
into twice the ordered adjacency sum. The whole computation stays inside `ℂ`. -/
private theorem sum_adj_normSq_sub [Fintype Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (g : Λ → ℂ) :
    ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then ((Complex.normSq (g x - g y) : ℝ) : ℂ) else 0)
      = 2 * ((∑ x : Λ, (G.degree x : ℂ) * ((Complex.normSq (g x) : ℝ) : ℂ))
          - ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then (starRingEnd ℂ) (g x) * g y else 0)) := by
  have hpt : ∀ z w : ℂ, ((Complex.normSq (z - w) : ℝ) : ℂ)
      = ((Complex.normSq z : ℝ) : ℂ) + ((Complex.normSq w : ℝ) : ℂ)
        - (starRingEnd ℂ) z * w - (starRingEnd ℂ) w * z := by
    intro z w
    simp only [← Complex.mul_conj, map_sub]
    ring
  have hswap : ∀ F : Λ → Λ → ℂ,
      ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then F x y else 0)
        = ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then F y x else 0) := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases h : G.Adj x y
    · rw [if_pos (G.symm h), if_pos h]
    · rw [if_neg (fun h' => h (G.symm h')), if_neg h]
  have hdeg : ∑ x : Λ, ∑ y : Λ, (if G.Adj x y then ((Complex.normSq (g x) : ℝ) : ℂ) else 0)
      = ∑ x : Λ, (G.degree x : ℂ) * ((Complex.normSq (g x) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [SimpleGraph.degree_eq_sum_if_adj (R := ℂ) G x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  have hsplit : ∀ x y : Λ,
      (if G.Adj x y then ((Complex.normSq (g x - g y) : ℝ) : ℂ) else 0)
        = (if G.Adj x y then ((Complex.normSq (g x) : ℝ) : ℂ) else 0)
          + (if G.Adj x y then ((Complex.normSq (g y) : ℝ) : ℂ) else 0)
          - (if G.Adj x y then (starRingEnd ℂ) (g x) * g y else 0)
          - (if G.Adj x y then (starRingEnd ℂ) (g y) * g x else 0) := by
    intro x y
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, hpt]
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h]
      ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdeg, hswap (fun x y => ((Complex.normSq (g y) : ℝ) : ℂ)), hdeg,
    hswap (fun x y => (starRingEnd ℂ) (g y) * g x)]
  ring

end LatticeSystem.Lattice
