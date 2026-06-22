import LatticeSystem.Quantum.SpinS.DressedHeisenbergRaiseLowerCore

/-!
# Marshall-dressed Heisenberg matrix elements on raise/lower steps
(Tasaki §2.5 Phase B-γ γ-3 irreducibility prep)

For a bipartite sublattice indicator `A x ≠ A y` on a graph edge
`(x, y)`, a raise/lower step `σ ↦ σ'` flips the Marshall sign factor
to `-1`. Combined with the strict positivity of the Heisenberg
matrix element on the same step (PR #805), the dressed-Heisenberg
matrix element is *strictly negative*:

    `Re (dressedHeisenbergS A J N σ' σ) < 0`.

This is the "non-zero off-diagonal entries" input needed to apply
Perron–Frobenius to the dressed matrix on a magnetization subspace
(Tasaki Theorem 2.2 for general spin).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Real-matrix versions -/

/-- The real-valued dressed Heisenberg matrix entry on a bipartite
raise/lower step is *strictly negative*. -/
theorem dressedHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergSReMatrix A J N σ' σ < 0 := by
  rw [dressedHeisenbergSReMatrix_apply]
  exact dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness A N hadj
    hAne hJ_real hJ_pos hJ_sym hsh hagree

/-- The real-valued dressed Heisenberg matrix entry on a bipartite
raise/lower step is non-zero. -/
theorem dressedHeisenbergSReMatrix_apply_ne_zero_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergSReMatrix A J N σ' σ ≠ 0 := by
  intro heq
  have hneg := dressedHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_witness
    A N hadj hAne hJ_real hJ_pos hJ_sym hsh hagree
  rw [heq] at hneg
  simp at hneg

/-! ## Negation: positive entries on raise/lower steps -/

/-- The negation of the real-valued dressed Heisenberg matrix has
*strictly positive* entries on bipartite raise/lower step witnesses,
the form needed for direct application of the matrix-power positivity
lift (PR #815) toward Perron–Frobenius irreducibility. -/
theorem neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < (-dressedHeisenbergSReMatrix A J N) σ' σ := by
  have hneg := dressedHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_witness
    A N hadj hAne hJ_real hJ_pos hJ_sym hsh hagree
  change 0 < -dressedHeisenbergSReMatrix A J N σ' σ
  linarith

/-- For a `RaiseLowerStepS` in the bipartite complete graph
`bipartiteCompleteGraphOf A` (so the witness sites are automatically
bipartite), the negation `-dressedHeisenbergSReMatrix` has strictly
positive entries between the two configurations:

    `0 < (-dressedHeisenbergSReMatrix A J N) τ σ`. -/
theorem neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : V → Fin (N + 1)}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < (-dressedHeisenbergSReMatrix A J N) τ σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  -- A x ≠ A y from bipartiteCompleteGraphOf adjacency.
  have hAne : A x ≠ A y := bipartiteCompleteGraphOf_adj_sublattice_ne hadj
  exact neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness A N
    hadj hAne (hJ_real x y) (hJ_pos x y hadj) (hJ_sym x y) hsh hagree

end LatticeSystem.Quantum
