import LatticeSystem.Quantum.SpinS.GraphLocalStarLowerBoundCore

/-!
# Product-indexed graph-local star blocks

This file continues Tasaki §2.5 Problem 2.5.b by reindexing a graph-local
star Hamiltonian into star coordinates and outside coordinates.  The reindexed
matrix is block diagonal in the outside coordinate, and each diagonal block is
the option-star Hamiltonian from the single-cluster transport bridge.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Rayleigh decomposition over outside blocks -/

/-- Multiplying the product-coordinate graph-local star by a vector is the same
as multiplying each fixed-outside block by the option-star Hamiltonian. -/
theorem graphLocalClusterHamiltonianS_product_mulVec
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (v : ((Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) → ℂ)
    (τ' : Option (G.neighborFinset x) → Fin (N + 1))
    (η : graphLocalOutsideSite G x → Fin (N + 1)) :
    (graphLocalClusterHamiltonianS_product G x N).mulVec v (τ', η) =
      (optionClusterHamiltonianS (G.neighborFinset x) N).mulVec
        (fun τ => v (τ, η)) τ' := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [Finset.sum_eq_single η]
  · change graphLocalClusterHamiltonianS_product G x N (τ', η) (τ, η) *
        v (τ, η) =
      optionClusterHamiltonianS (G.neighborFinset x) N τ' τ *
        v (τ, η)
    rw [graphLocalClusterHamiltonianS_product_apply_of_outside_eq G x N
      (τ', η) (τ, η) rfl]
  · intro η' _ hη'
    change graphLocalClusterHamiltonianS_product G x N (τ', η) (τ, η') *
        v (τ, η') = 0
    rw [graphLocalClusterHamiltonianS_product_apply_of_outside_ne G x N
      (τ', η) (τ, η') (by
        intro h
        exact hη' h.symm)]
    simp
  · intro hη
    exact False.elim (hη (Finset.mem_univ η))

/-! ## Reindexing Rayleigh quotients -/

/-- Reindexing a matrix and pulling a vector back along the same equivalence
commutes with matrix-vector multiplication. -/
theorem matrix_mulVec_reindex_comp_symm
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix α α ℂ) (v : α → ℂ) :
    (Matrix.reindex e e M).mulVec (v ∘ e.symm) = (M.mulVec v) ∘ e.symm := by
  ext b
  unfold Matrix.mulVec dotProduct
  simpa [Matrix.reindex_apply, Function.comp_def] using
    (e.symm.sum_comp (fun a => M (e.symm b) a * v a))

/-- Pulling both entries of a dot product back along an equivalence leaves the
dot product unchanged. -/
theorem dotProduct_comp_equiv_symm
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (v : α → ℂ) :
    dotProduct (star (v ∘ e.symm)) (v ∘ e.symm) =
      dotProduct (star v) v := by
  unfold dotProduct
  simpa [Function.comp_def, Pi.star_apply] using
    (e.symm.sum_comp (fun a => star (v a) * v a))

/-- Reindexing a matrix and pulling a vector back along the same equivalence
does not change its Rayleigh numerator. -/
theorem rayleighOnVec_reindex_comp_symm
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix α α ℂ) (v : α → ℂ) :
    rayleighOnVec (Matrix.reindex e e M) (v ∘ e.symm) =
      rayleighOnVec M v := by
  unfold rayleighOnVec
  rw [matrix_mulVec_reindex_comp_symm e M v]
  unfold dotProduct
  exact congrArg Complex.re <| by
    simpa [Function.comp_def, Pi.star_apply] using
      (e.symm.sum_comp (fun a => star (v a) * M.mulVec v a))

/-- The squared norm of a product-indexed vector is the sum of the squared norms
of its fixed-outside blocks. -/
theorem dotProduct_product_re_eq_sum_blocks
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (v : ((Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) → ℂ) :
    (dotProduct (star v) v).re =
      ∑ η : graphLocalOutsideSite G x → Fin (N + 1),
        (dotProduct (star (fun τ => v (τ, η))) (fun τ => v (τ, η))).re := by
  classical
  unfold dotProduct
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro η _
  rw [Complex.re_sum]
  simp [Pi.star_apply]

/-- The Rayleigh numerator of the product-coordinate graph-local star is the sum
of the Rayleigh numerators of its fixed-outside option-star blocks. -/
theorem rayleighOnVec_graphLocalClusterHamiltonianS_product
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (v : ((Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) → ℂ) :
    rayleighOnVec (graphLocalClusterHamiltonianS_product G x N) v =
      ∑ η : graphLocalOutsideSite G x → Fin (N + 1),
        rayleighOnVec (optionClusterHamiltonianS (G.neighborFinset x) N)
          (fun τ => v (τ, η)) := by
  classical
  unfold rayleighOnVec dotProduct
  simp_rw [graphLocalClusterHamiltonianS_product_mulVec G x N v]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro η _
  rw [Complex.re_sum]
  simp [Pi.star_apply]

/-- If every option-star block has Rayleigh lower bound `ε`, then the
product-coordinate graph-local star has the same Rayleigh lower bound. -/
theorem graphLocalClusterHamiltonianS_product_rayleigh_lower
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {ε : ℝ}
    (hblock : ∀ _η : graphLocalOutsideSite G x → Fin (N + 1),
      ∀ w : (Option (G.neighborFinset x) → Fin (N + 1)) → ℂ,
        ε * (dotProduct (star w) w).re ≤
          rayleighOnVec (optionClusterHamiltonianS (G.neighborFinset x) N) w)
    (v : ((Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) → ℂ) :
    ε * (dotProduct (star v) v).re ≤
      rayleighOnVec (graphLocalClusterHamiltonianS_product G x N) v := by
  classical
  rw [dotProduct_product_re_eq_sum_blocks G x N v]
  rw [rayleighOnVec_graphLocalClusterHamiltonianS_product G x N v]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun η _ => hblock η (fun τ => v (τ, η)))

/-- If every option-star block has Rayleigh lower bound `ε`, then the
product-coordinate graph-local star has Hermitian minimum eigenvalue at least
`ε`. -/
theorem graphLocalClusterHamiltonianS_product_minEigenvalue_lower
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {ε : ℝ}
    (hblock : ∀ _η : graphLocalOutsideSite G x → Fin (N + 1),
      ∀ w : (Option (G.neighborFinset x) → Fin (N + 1)) → ℂ,
        ε * (dotProduct (star w) w).re ≤
          rayleighOnVec (optionClusterHamiltonianS (G.neighborFinset x) N) w) :
    ε ≤ hermitianMinEigenvalue
      (graphLocalClusterHamiltonianS_product_isHermitian G x N) := by
  obtain ⟨v, hunit, hv⟩ :=
    exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue
      (graphLocalClusterHamiltonianS_product_isHermitian G x N)
  have h := graphLocalClusterHamiltonianS_product_rayleigh_lower G x N hblock v
  rw [hunit] at h
  simpa [hv] using h

/-! ## Lower bound on the original graph-local star -/

/-- If every option-star block has Rayleigh lower bound `ε`, then the original
same-Hilbert-space graph-local star has the same Rayleigh lower bound. -/
theorem graphLocalClusterHamiltonianS_rayleigh_lower
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {ε : ℝ}
    (hblock : ∀ _η : graphLocalOutsideSite G x → Fin (N + 1),
      ∀ w : (Option (G.neighborFinset x) → Fin (N + 1)) → ℂ,
        ε * (dotProduct (star w) w).re ≤
          rayleighOnVec (optionClusterHamiltonianS (G.neighborFinset x) N) w)
    (v : (Λ → Fin (N + 1)) → ℂ) :
    ε * (dotProduct (star v) v).re ≤
      rayleighOnVec (graphLocalClusterHamiltonianS G x N) v := by
  let e := graphLocalConfigEquiv G x N
  let vp :
      ((Option (G.neighborFinset x) → Fin (N + 1)) ×
        (graphLocalOutsideSite G x → Fin (N + 1))) → ℂ :=
    v ∘ e.symm
  have hprod := graphLocalClusterHamiltonianS_product_rayleigh_lower G x N hblock vp
  have hnorm :
      (dotProduct (star vp) vp).re = (dotProduct (star v) v).re := by
    dsimp [vp, e]
    rw [dotProduct_comp_equiv_symm]
  have hray :
      rayleighOnVec (graphLocalClusterHamiltonianS_product G x N) vp =
        rayleighOnVec (graphLocalClusterHamiltonianS G x N) v := by
    dsimp [vp, e]
    unfold graphLocalClusterHamiltonianS_product
    rw [rayleighOnVec_reindex_comp_symm]
  rwa [hnorm, hray] at hprod

/-- If every option-star block has Rayleigh lower bound `ε`, then the original
same-Hilbert-space graph-local star has Hermitian minimum eigenvalue at least
`ε`. -/
theorem graphLocalClusterHamiltonianS_minEigenvalue_lower
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {ε : ℝ}
    (hblock : ∀ _η : graphLocalOutsideSite G x → Fin (N + 1),
      ∀ w : (Option (G.neighborFinset x) → Fin (N + 1)) → ℂ,
        ε * (dotProduct (star w) w).re ≤
          rayleighOnVec (optionClusterHamiltonianS (G.neighborFinset x) N) w) :
    ε ≤ hermitianMinEigenvalue (graphLocalClusterHamiltonianS_isHermitian G x N) := by
  obtain ⟨v, hunit, hv⟩ :=
    exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue
      (graphLocalClusterHamiltonianS_isHermitian G x N)
  have h := graphLocalClusterHamiltonianS_rayleigh_lower G x N hblock v
  rw [hunit] at h
  simpa [hv] using h

end LatticeSystem.Quantum
