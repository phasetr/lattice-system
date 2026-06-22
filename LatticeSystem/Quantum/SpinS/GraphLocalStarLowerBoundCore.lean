import LatticeSystem.Quantum.SpinS.GraphLocalStarBlock
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# Graph-local star Hamiltonian: product coordinates (foundation)

Foundational layer extracted from `GraphLocalStarLowerBound.lean` for build speed.
This file builds the product-coordinate description of one graph-local star
(`graphLocalOutsideSite`, `graphLocalProductConfig`, `graphLocalConfigEquiv` and its
computation rules) and the product cluster Hamiltonian `graphLocalClusterHamiltonianS_product`
with its Hermiticity (`graphLocalClusterHamiltonianS_product_isHermitian`) and outside-block
apply lemmas (`graphLocalClusterHamiltonianS_product_apply_of_outside_eq`/`_ne`).

The product `mulVec` action, the reindexed graph-local star matrix entries
(`matrix_mulVec_reindex_comp_symm`, `rayleighOnVec_reindex_comp_symm`, …), the Rayleigh
decomposition over outside blocks, and the lower bound on the original graph-local star
(`graphLocalClusterHamiltonianS_minEigenvalue_lower`) are kept in the capstone module
`GraphLocalStarLowerBound.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Product coordinates for one graph-local star -/

/-- Sites outside the local star centered at `x`: neither the center nor a graph
neighbor of the center. -/
def graphLocalOutsideSite (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) :=
  {z : Λ // z ≠ x ∧ z ∉ G.neighborFinset x}

/-- The outside-site subtype is finite when the ambient graph vertex type is
finite. -/
instance graphLocalOutsideSite_fintype
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) :
    Fintype (graphLocalOutsideSite G x) :=
  Subtype.fintype _

/-- The outside-site subtype inherits decidable equality from the ambient vertex
type. -/
instance graphLocalOutsideSite_decidableEq
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) :
    DecidableEq (graphLocalOutsideSite G x) :=
  by
    change DecidableEq {z : Λ // z ≠ x ∧ z ∉ G.neighborFinset x}
    infer_instance

/-- Extend an outside assignment to a full configuration.  Values on the center
and neighbor sites are irrelevant for fixed-outside block statements, so they
are filled with `0`. -/
def graphLocalOutsideConfigExtend
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : graphLocalOutsideSite G x → Fin (N + 1)) :
    Λ → Fin (N + 1) :=
  fun z =>
    if h : z ≠ x ∧ z ∉ G.neighborFinset x then η ⟨z, h⟩ else 0

/-- Product-coordinate reconstruction of a full configuration from a star
configuration and an outside assignment. -/
def graphLocalProductConfig
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (p : (Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) :
    Λ → Fin (N + 1) :=
  graphLocalStarConfig G x N (graphLocalOutsideConfigExtend G x N p.2) p.1

/-- Full configurations are equivalently star configurations paired with outside
assignments. -/
def graphLocalConfigEquiv
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    (Λ → Fin (N + 1)) ≃
      ((Option (G.neighborFinset x) → Fin (N + 1)) ×
        (graphLocalOutsideSite G x → Fin (N + 1))) where
  toFun σ :=
    (fun o =>
      match o with
      | none => σ x
      | some y => σ y,
    fun z => σ z.1)
  invFun p := graphLocalProductConfig G x N p
  left_inv σ := by
    funext z
    by_cases hzx : z = x
    · subst hzx
      simp [graphLocalProductConfig]
    · by_cases hzmem : z ∈ G.neighborFinset x
      · change graphLocalStarConfig G x N
          (graphLocalOutsideConfigExtend G x N
            (fun z : graphLocalOutsideSite G x => σ z.1))
          (fun o =>
            match o with
            | none => σ x
            | some y => σ y) z = σ z
        simpa using graphLocalStarConfig_neighbor G x N
          (graphLocalOutsideConfigExtend G x N
            (fun z : graphLocalOutsideSite G x => σ z.1))
          (fun o =>
            match o with
            | none => σ x
            | some y => σ y) ⟨z, hzmem⟩
      · change graphLocalStarConfig G x N
          (graphLocalOutsideConfigExtend G x N
            (fun z : graphLocalOutsideSite G x => σ z.1))
          (fun o =>
            match o with
            | none => σ x
            | some y => σ y) z = σ z
        rw [graphLocalStarConfig_outside G x N
          (graphLocalOutsideConfigExtend G x N
            (fun z : graphLocalOutsideSite G x => σ z.1)) _ hzx hzmem]
        simp [graphLocalOutsideConfigExtend, hzx, hzmem]
  right_inv p := by
    rcases p with ⟨τ, η⟩
    ext o
    · cases o <;> simp [graphLocalProductConfig]
    · have h := graphLocalStarConfig_outside G x N
        (graphLocalOutsideConfigExtend G x N η) τ o.property.1 o.property.2
      simp [graphLocalProductConfig, graphLocalOutsideConfigExtend, o.property] at h ⊢

/-- Evaluating `graphLocalConfigEquiv` at the center component. -/
@[simp] theorem graphLocalConfigEquiv_apply_none
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) :
    (graphLocalConfigEquiv G x N σ).1 none = σ x := rfl

/-- Evaluating `graphLocalConfigEquiv` at a neighbor component. -/
@[simp] theorem graphLocalConfigEquiv_apply_some
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) (y : G.neighborFinset x) :
    (graphLocalConfigEquiv G x N σ).1 (some y) = σ y := rfl

/-- Evaluating `graphLocalConfigEquiv` at an outside component. -/
@[simp] theorem graphLocalConfigEquiv_apply_outside
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) (z : graphLocalOutsideSite G x) :
    (graphLocalConfigEquiv G x N σ).2 z = σ z.1 := rfl

/-- The inverse product-coordinate equivalence is `graphLocalProductConfig`. -/
@[simp] theorem graphLocalConfigEquiv_symm_apply
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (p : (Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1))) :
    (graphLocalConfigEquiv G x N).symm p = graphLocalProductConfig G x N p := rfl

/-- Product reconstruction reads the outside assignment on outside sites. -/
@[simp] theorem graphLocalProductConfig_outside
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (p : (Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1)))
    (z : graphLocalOutsideSite G x) :
    graphLocalProductConfig G x N p z.1 = p.2 z := by
  rw [graphLocalProductConfig]
  rw [graphLocalStarConfig_outside G x N
    (graphLocalOutsideConfigExtend G x N p.2) p.1 z.property.1 z.property.2]
  simp [graphLocalOutsideConfigExtend, z.property]

/-! ## Reindexed graph-local star matrix entries -/

/-- The graph-local star Hamiltonian reindexed by star/outside product
coordinates. -/
noncomputable def graphLocalClusterHamiltonianS_product
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    Matrix
      ((Option (G.neighborFinset x) → Fin (N + 1)) ×
        (graphLocalOutsideSite G x → Fin (N + 1)))
      ((Option (G.neighborFinset x) → Fin (N + 1)) ×
        (graphLocalOutsideSite G x → Fin (N + 1))) ℂ :=
  Matrix.reindex (graphLocalConfigEquiv G x N) (graphLocalConfigEquiv G x N)
    (graphLocalClusterHamiltonianS G x N)

/-- The product-coordinate graph-local star Hamiltonian is Hermitian. -/
theorem graphLocalClusterHamiltonianS_product_isHermitian
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    (graphLocalClusterHamiltonianS_product G x N).IsHermitian := by
  unfold graphLocalClusterHamiltonianS_product
  exact (graphLocalClusterHamiltonianS_isHermitian G x N).reindex
    (graphLocalConfigEquiv G x N)

/-- On a fixed outside block, the reindexed graph-local star is the option-star
Hamiltonian. -/
theorem graphLocalClusterHamiltonianS_product_apply_of_outside_eq
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (p' p : (Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1)))
    (hη : p'.2 = p.2) :
    graphLocalClusterHamiltonianS_product G x N p' p =
      optionClusterHamiltonianS (G.neighborFinset x) N p'.1 p.1 := by
  unfold graphLocalClusterHamiltonianS_product
  rw [Matrix.reindex_apply]
  change (graphLocalClusterHamiltonianS G x N).submatrix
      (graphLocalProductConfig G x N ∘ fun τ =>
        (τ, p'.2))
      (graphLocalProductConfig G x N ∘ fun τ =>
        (τ, p.2)) p'.1 p.1 =
    optionClusterHamiltonianS (G.neighborFinset x) N p'.1 p.1
  rw [hη]
  rw [show (graphLocalProductConfig G x N ∘ fun τ =>
        (τ, p.2)) =
      graphLocalStarConfig G x N (graphLocalOutsideConfigExtend G x N p.2) by
    funext τ
    rfl]
  exact congrFun₂
    (graphLocalClusterHamiltonianS_block_eq_optionClusterHamiltonianS G x N
      (graphLocalOutsideConfigExtend G x N p.2)) p'.1 p.1

/-- Different outside blocks do not couple in the reindexed graph-local star. -/
theorem graphLocalClusterHamiltonianS_product_apply_of_outside_ne
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (p' p : (Option (G.neighborFinset x) → Fin (N + 1)) ×
      (graphLocalOutsideSite G x → Fin (N + 1)))
    (hη : p'.2 ≠ p.2) :
    graphLocalClusterHamiltonianS_product G x N p' p = 0 := by
  unfold graphLocalClusterHamiltonianS_product
  rw [Matrix.reindex_apply]
  apply graphLocalClusterHamiltonianS_apply_eq_zero_of_outside_diff
  intro hout
  apply hη
  funext z
  simpa [graphLocalConfigEquiv_symm_apply, graphLocalProductConfig_outside] using
    hout z.1 z.property.1 z.property.2

end LatticeSystem.Quantum
