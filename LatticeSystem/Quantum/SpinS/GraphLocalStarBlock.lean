import LatticeSystem.Quantum.SpinS.HeisenbergGraphLocal
import LatticeSystem.Quantum.SpinS.SingleClusterTransport

/-!
# Fixed-outside blocks of graph-local star Hamiltonians

This file adds the block-level bridge needed for Tasaki §2.5 Problem 2.5.b:
after fixing the spins outside a center `x` and its graph neighbors, the
same-Hilbert-space graph-local star Hamiltonian centered at `x` has the same
matrix entries as the finite option-star Hamiltonian on
`Option (G.neighborFinset x)`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Embedding fixed-outside star configurations into the full Hilbert space -/

/-- The full configuration obtained from a star configuration
`τ : Option (G.neighborFinset x) → Fin (N + 1)` and a fixed outside
configuration `η`.  The center `x` is read from `τ none`, neighbors are read
from `τ (some y)`, and all other sites are read from `η`. -/
def graphLocalStarConfig
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) (τ : Option (G.neighborFinset x) → Fin (N + 1)) :
    Λ → Fin (N + 1) :=
  fun v =>
    if v = x then τ none
    else if hmem : v ∈ G.neighborFinset x then τ (some ⟨v, hmem⟩)
    else η v

/-- At the center, the embedded star configuration reads the `none` component. -/
@[simp] theorem graphLocalStarConfig_center
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) (τ : Option (G.neighborFinset x) → Fin (N + 1)) :
    graphLocalStarConfig G x N η τ x = τ none := by
  unfold graphLocalStarConfig
  rw [if_pos rfl]

/-- At a graph neighbor, the embedded star configuration reads the corresponding
`some` component. -/
@[simp] theorem graphLocalStarConfig_neighbor
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) (τ : Option (G.neighborFinset x) → Fin (N + 1))
    (y : G.neighborFinset x) :
    graphLocalStarConfig G x N η τ y = τ (some y) := by
  unfold graphLocalStarConfig
  have hyadj : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp y.property
  have hyne : (y : Λ) ≠ x := (G.ne_of_adj hyadj).symm
  rw [if_neg hyne, dif_pos y.property]

/-- Away from the center and graph neighbors, the embedded star configuration
reads the fixed outside configuration. -/
@[simp] theorem graphLocalStarConfig_outside
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) (τ : Option (G.neighborFinset x) → Fin (N + 1))
    {v : Λ} (hvx : v ≠ x) (hv : v ∉ G.neighborFinset x) :
    graphLocalStarConfig G x N η τ v = η v := by
  unfold graphLocalStarConfig
  rw [if_neg hvx, dif_neg hv]

/-! ## Matrix-entry comparison for one star edge -/

/-- For a neighbor `y` of `x`, embedded full configurations agree off `{x, y}`
whenever the corresponding option-star configurations agree off
`{none, some y}`. -/
theorem graphLocalStarConfig_agree_off_pair_of_option_agree
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1))
    {τ' τ : Option (G.neighborFinset x) → Fin (N + 1)}
    (y : G.neighborFinset x)
    (hτ : ∀ k : Option (G.neighborFinset x),
      k ≠ none → k ≠ some y → τ' k = τ k) :
    ∀ k : Λ, k ≠ x → k ≠ y →
      graphLocalStarConfig G x N η τ' k =
        graphLocalStarConfig G x N η τ k := by
  intro k hkx hky
  by_cases hk : k ∈ G.neighborFinset x
  · have hsome_ne : (some ⟨k, hk⟩ : Option (G.neighborFinset x)) ≠ some y := by
      intro h
      apply hky
      exact congrArg Subtype.val (Option.some.inj h)
    rw [graphLocalStarConfig_neighbor G x N η τ' ⟨k, hk⟩,
      graphLocalStarConfig_neighbor G x N η τ ⟨k, hk⟩]
    exact hτ (some ⟨k, hk⟩) (by simp) hsome_ne
  · rw [graphLocalStarConfig_outside G x N η τ' hkx hk,
      graphLocalStarConfig_outside G x N η τ hkx hk]

/-- If embedded full configurations agree off `{x, y}`, then the underlying
option-star configurations agree off `{none, some y}`. -/
theorem option_agree_of_graphLocalStarConfig_agree_off_pair
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1))
    {τ' τ : Option (G.neighborFinset x) → Fin (N + 1)}
    (y : G.neighborFinset x)
    (hfull : ∀ k : Λ, k ≠ x → k ≠ y →
      graphLocalStarConfig G x N η τ' k =
        graphLocalStarConfig G x N η τ k) :
    ∀ k : Option (G.neighborFinset x),
      k ≠ none → k ≠ some y → τ' k = τ k := by
  intro k hk_none hk_y
  cases k with
  | none => exact False.elim (hk_none rfl)
  | some z =>
      have hzadj : G.Adj x z := (SimpleGraph.mem_neighborFinset G x z).mp z.property
      have hzx : (z : Λ) ≠ x := (G.ne_of_adj hzadj).symm
      have hzy : (z : Λ) ≠ y := by
        intro h
        apply hk_y
        exact congrArg some (Subtype.ext h)
      have h := hfull z hzx hzy
      simpa [graphLocalStarConfig_neighbor] using h

/-- The matrix element of a full graph-local star edge on an embedded
fixed-outside block equals the corresponding option-star edge matrix element. -/
theorem spinSDot_graphLocalStarConfig_eq_option
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1))
    (τ' τ : Option (G.neighborFinset x) → Fin (N + 1))
    (y : G.neighborFinset x) :
    (spinSDot x y N : ManyBodyOpS Λ N)
        (graphLocalStarConfig G x N η τ') (graphLocalStarConfig G x N η τ) =
      (spinSDot none (some y) N :
        ManyBodyOpS (Option (G.neighborFinset x)) N) τ' τ := by
  have hyadj : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp y.property
  have hxy : x ≠ (y : Λ) := G.ne_of_adj hyadj
  have hopt_xy : (none : Option (G.neighborFinset x)) ≠ some y := by simp
  by_cases hτ : ∀ k : Option (G.neighborFinset x),
      k ≠ none → k ≠ some y → τ' k = τ k
  · have hfull :=
      graphLocalStarConfig_agree_off_pair_of_option_agree G x N η y hτ
    rw [spinSDot_apply_of_off_two_site_agree hxy N hfull,
      spinSDot_apply_of_off_two_site_agree hopt_xy N hτ]
    simp [graphLocalStarConfig_center, graphLocalStarConfig_neighbor]
  · have hoption_zero :
        (spinSDot none (some y) N :
          ManyBodyOpS (Option (G.neighborFinset x)) N) τ' τ = 0 := by
      exact spinSDot_apply_eq_zero_of_off_two_site_diff hopt_xy N hτ
    have hfull_not :
        ¬ ∀ k : Λ, k ≠ x → k ≠ y →
          graphLocalStarConfig G x N η τ' k =
            graphLocalStarConfig G x N η τ k := by
      intro hfull
      exact hτ (option_agree_of_graphLocalStarConfig_agree_off_pair G x N η y hfull)
    rw [spinSDot_apply_eq_zero_of_off_two_site_diff hxy N hfull_not, hoption_zero]

/-! ## Block identity for graph-local star Hamiltonians -/

/-- If two full configurations differ outside the center and its graph
neighbors, the graph-local star Hamiltonian centered at `x` has zero matrix
entry between them. -/
theorem graphLocalClusterHamiltonianS_apply_eq_zero_of_outside_diff
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k : Λ, k ≠ x → k ∉ G.neighborFinset x → σ' k = σ k) :
    (graphLocalClusterHamiltonianS G x N : ManyBodyOpS Λ N) σ' σ = 0 := by
  unfold graphLocalClusterHamiltonianS
  rw [Matrix.sum_apply]
  change (∑ y ∈ G.neighborFinset x,
      (spinSDot x y N : ManyBodyOpS Λ N) σ' σ) = 0
  rw [Finset.sum_eq_zero]
  intro y hy
  have hyadj : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
  have hxy : x ≠ y := G.ne_of_adj hyadj
  apply spinSDot_apply_eq_zero_of_off_two_site_diff hxy N
  intro hagree
  apply h
  intro k hkx hknot
  exact hagree k hkx (by
    intro hky
    apply hknot
    rw [hky]
    exact hy)

/-- The fixed-outside block of the same-Hilbert-space graph-local star
Hamiltonian is the finite option-star Hamiltonian on the center and neighbor
set. -/
theorem graphLocalClusterHamiltonianS_block_eq_optionClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) :
    (graphLocalClusterHamiltonianS G x N).submatrix
        (graphLocalStarConfig G x N η) (graphLocalStarConfig G x N η) =
      optionClusterHamiltonianS (G.neighborFinset x) N := by
  ext τ' τ
  unfold graphLocalClusterHamiltonianS optionClusterHamiltonianS
  rw [Matrix.submatrix_apply]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  change (∑ y ∈ G.neighborFinset x,
      (spinSDot x y N : ManyBodyOpS Λ N)
        (graphLocalStarConfig G x N η τ')
        (graphLocalStarConfig G x N η τ)) =
    ∑ y : G.neighborFinset x,
      (spinSDot none (some y) N :
        ManyBodyOpS (Option (G.neighborFinset x)) N) τ' τ
  rw [← Finset.sum_attach (s := G.neighborFinset x)
    (f := fun y =>
      (spinSDot x y N : ManyBodyOpS Λ N)
        (graphLocalStarConfig G x N η τ')
        (graphLocalStarConfig G x N η τ))]
  refine Finset.sum_congr rfl ?_
  intro y _
  exact spinSDot_graphLocalStarConfig_eq_option G x N η τ' τ y

end LatticeSystem.Quantum
