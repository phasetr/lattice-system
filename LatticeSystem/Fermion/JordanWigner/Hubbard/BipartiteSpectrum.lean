import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Bipartite single-electron spectrum (Tasaki §10.2.3, Proposition 10.7)

This file formalizes **Tasaki Proposition 10.7** (Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3,
p. 356): for a real symmetric bipartite hopping matrix `T` (`Λ = A ⊔ B`,
hopping only across the sublattices),

1. the single-electron spectrum is **symmetric about zero**: this is proved
   in the multiplicity (characteristic-polynomial) form
   `(-T).charpoly = T.charpoly`, via the diagonal gauge transformation
   `D T D = -T` with `D = diag(±1)` (`+1` on `A`, `−1` on `B`);
2. there are **at least `|A| − |B|` zero eigenvalues**: the kernel of `T`
   (the zero-energy single-electron states) has dimension at least
   `|A| − |B|`, because `T` maps the `|A|`-dimensional `A`-supported
   subspace into the `|B|`-dimensional `B`-supported subspace.

Unlike the reflection-positivity results of §10.2, this is finite-dimensional
linear algebra and is **proved sorry-free**.

The bipartition vocabulary (`HoppingRespectsBipartition`,
`bipartitionComplement`) is reused from `LiebRepulsive.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The bipartite gauge sign: `+1` on the sublattice `A`, `−1` on its
complement `B = Aᶜ`. -/
noncomputable def bipartiteSign (A : Finset (Fin (N + 1))) (x : Fin (N + 1)) : ℝ :=
  if x ∈ A then 1 else -1

/-- The diagonal `±1` matrix implementing the bipartite gauge transform. -/
noncomputable def bipartiteSignMatrix (A : Finset (Fin (N + 1))) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal (bipartiteSign A)

/-- The bipartite sign matrix squares to the identity (`D² = 1`). -/
theorem bipartiteSignMatrix_mul_self (A : Finset (Fin (N + 1))) :
    bipartiteSignMatrix A * bipartiteSignMatrix A = 1 := by
  rw [bipartiteSignMatrix, Matrix.diagonal_mul_diagonal]
  rw [show (fun x => bipartiteSign A x * bipartiteSign A x) = (fun _ => (1 : ℝ)) from ?_,
    ← Matrix.diagonal_one]
  funext x
  unfold bipartiteSign
  split <;> norm_num

/-- A hopping matrix respecting the bipartition changes sign under the
diagonal gauge: `D T D = -T` (Tasaki's `ϕ ↦ ϕ̃` sign flip). -/
theorem bipartiteSignMatrix_mul_hopping_mul (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : HoppingRespectsBipartition A T) :
    bipartiteSignMatrix A * T * bipartiteSignMatrix A = -T := by
  ext x y
  simp only [bipartiteSignMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.neg_apply]
  by_cases hxy : T x y = 0
  · simp [hxy]
  · have hop := hT hxy
    unfold bipartiteSign
    by_cases hx : x ∈ A
    · have hy : y ∉ A := hop.mp hx
      rw [if_pos hx, if_neg hy]; ring
    · have hy : y ∈ A := not_not.mp fun hyna => hx (hop.mpr hyna)
      rw [if_neg hx, if_pos hy]; ring

/-- **Tasaki Proposition 10.7(i)** (multiplicity form). For a bipartite
hopping matrix `T`, the characteristic polynomial is invariant under
`T ↦ -T`, so the single-electron spectrum is symmetric about zero with
multiplicity: `(-T).charpoly = T.charpoly`. -/
theorem proposition_10_7_charpoly_neg_eq (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : HoppingRespectsBipartition A T) :
    (-T).charpoly = T.charpoly := by
  have hD2 := bipartiteSignMatrix_mul_self A
  have hDTD := bipartiteSignMatrix_mul_hopping_mul A T hT
  rw [← hDTD, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hD2, Matrix.one_mul]

/-! ### Proposition 10.7(ii): the zero-mode lower bound -/

/-- The extend-by-zero linear map sending an `S`-supported coordinate vector to
the full vector on `Fin (N+1)` (zero outside `S`). -/
noncomputable def extByZero (S : Finset (Fin (N + 1))) :
    ({x // x ∈ S} → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) where
  toFun a := fun x => if h : x ∈ S then a ⟨x, h⟩ else 0
  map_add' a b := by funext x; by_cases h : x ∈ S <;> simp [h]
  map_smul' c a := by funext x; by_cases h : x ∈ S <;> simp [h]

/-- `extByZero S a x = a ⟨x, hx⟩` at a site `x ∈ S`. -/
theorem extByZero_apply_of_mem (S : Finset (Fin (N + 1))) (a : {x // x ∈ S} → ℝ)
    {x : Fin (N + 1)} (hx : x ∈ S) : extByZero S a x = a ⟨x, hx⟩ := by
  simp only [extByZero, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]

/-- `extByZero S a x = 0` at a site `x ∉ S`. -/
theorem extByZero_apply_of_not_mem (S : Finset (Fin (N + 1))) (a : {x // x ∈ S} → ℝ)
    {x : Fin (N + 1)} (hx : x ∉ S) : extByZero S a x = 0 := by
  simp only [extByZero, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hx]

/-- `extByZero S` is injective. -/
theorem extByZero_injective (S : Finset (Fin (N + 1))) :
    Function.Injective (extByZero S) := by
  intro a b hab
  funext x
  have := congrFun hab x.1
  simpa [extByZero, x.2] using this

/-- The range of `extByZero S` (the `S`-supported vectors) has dimension `|S|`. -/
theorem extByZero_finrank_range (S : Finset (Fin (N + 1))) :
    Module.finrank ℝ (LinearMap.range (extByZero S)) = S.card := by
  rw [LinearMap.finrank_range_of_inj (extByZero_injective S),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- The combinatorial complement equals the `Finset` complement. -/
theorem bipartitionComplement_eq_compl (A : Finset (Fin (N + 1))) :
    bipartitionComplement A = Aᶜ := by
  ext x
  simp [bipartitionComplement, Finset.mem_compl]

/-- For a hopping matrix respecting the bipartition, the image of an
`A`-supported vector vanishes on `A` (it lands on the complement `B`). -/
theorem hopping_extByZero_apply_mem_eq_zero (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : HoppingRespectsBipartition A T)
    (a : {x // x ∈ A} → ℝ) {x : Fin (N + 1)} (hx : x ∈ A) :
    T.mulVecLin (extByZero A a) x = 0 := by
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y ∈ A
  · by_cases hTxy : T x y = 0
    · rw [hTxy, zero_mul]
    · exact absurd ((hT hTxy).mp hx) (not_not.mpr hy)
  · rw [extByZero_apply_of_not_mem A a hy, mul_zero]

/-- The `A`-block of the hopping action: `a ↦ T (extByZero A a)`, sending an
`A`-supported vector through the hopping matrix. -/
noncomputable def bipartiteHoppingBlock (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ({x // x ∈ A} → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
  T.mulVecLin ∘ₗ extByZero A

@[simp]
theorem bipartiteHoppingBlock_apply (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (a : {x // x ∈ A} → ℝ) :
    bipartiteHoppingBlock A T a = T.mulVecLin (extByZero A a) :=
  rfl

/-- **Tasaki Proposition 10.7(ii)**. For a bipartite hopping matrix `T` with
`|B| ≤ |A|`, there are at least `|A| − |B|` zero-energy single-electron states:
the kernel of `T` has dimension at least `|A| − |B|`.

Proof: the block map `a ↦ T (extByZero A a)` sends `A`-supported vectors into
`B`-supported vectors (by bipartiteness), so its range has dimension `≤ |B|`;
rank–nullity over the `|A|`-dimensional domain gives a kernel of dimension
`≥ |A| − |B|`; and `extByZero A` injects that kernel into `ker T`. -/
theorem proposition_10_7_zero_mode_lower_bound (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : HoppingRespectsBipartition A T)
    (hcard : (bipartitionComplement A).card ≤ A.card) :
    A.card - (bipartitionComplement A).card ≤
      Module.finrank ℝ (LinearMap.ker T.mulVecLin) := by
  -- `range (block) ⊆ range (extByZero Aᶜ)`, the `B`-supported vectors.
  have hrange : LinearMap.range (bipartiteHoppingBlock A T) ≤
      LinearMap.range (extByZero Aᶜ) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨fun b => bipartiteHoppingBlock A T a b.1, ?_⟩
    funext x
    show extByZero Aᶜ (fun b => bipartiteHoppingBlock A T a b.1) x
      = bipartiteHoppingBlock A T a x
    by_cases hx : x ∈ A
    · have hxc : x ∉ (Aᶜ : Finset (Fin (N + 1))) := fun h => Finset.mem_compl.mp h hx
      rw [extByZero_apply_of_not_mem _ _ hxc, bipartiteHoppingBlock_apply]
      exact (hopping_extByZero_apply_mem_eq_zero A T hT a hx).symm
    · have hxc : x ∈ (Aᶜ : Finset (Fin (N + 1))) := Finset.mem_compl.mpr hx
      rw [extByZero_apply_of_mem _ _ hxc]
  -- Hence `finrank (range) ≤ |B|`.
  have hrange_le : Module.finrank ℝ (LinearMap.range (bipartiteHoppingBlock A T))
      ≤ (bipartitionComplement A).card := by
    refine (Submodule.finrank_mono hrange).trans ?_
    rw [extByZero_finrank_range, bipartitionComplement_eq_compl]
  -- Rank–nullity over the `|A|`-dimensional domain.
  have hrn := (bipartiteHoppingBlock A T).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  -- `finrank (ker) ≥ |A| − |B|`.
  have hkerL : A.card - (bipartitionComplement A).card ≤
      Module.finrank ℝ (LinearMap.ker (bipartiteHoppingBlock A T)) := by omega
  -- `extByZero A` injects `ker (block)` into `ker T`, preserving dimension.
  have hmap : (LinearMap.ker (bipartiteHoppingBlock A T)).map (extByZero A)
      ≤ LinearMap.ker T.mulVecLin := by
    rintro _ ⟨a, ha, rfl⟩
    rw [LinearMap.mem_ker]
    have hbz : bipartiteHoppingBlock A T a = 0 := ha
    rw [bipartiteHoppingBlock_apply] at hbz
    exact hbz
  have hfin_eq : Module.finrank ℝ (LinearMap.ker (bipartiteHoppingBlock A T))
      = Module.finrank ℝ ((LinearMap.ker (bipartiteHoppingBlock A T)).map (extByZero A)) :=
    (Submodule.equivMapOfInjective (extByZero A) (extByZero_injective A) _).finrank_eq
  calc A.card - (bipartitionComplement A).card
      ≤ Module.finrank ℝ (LinearMap.ker (bipartiteHoppingBlock A T)) := hkerL
    _ = Module.finrank ℝ ((LinearMap.ker (bipartiteHoppingBlock A T)).map (extByZero A)) := hfin_eq
    _ ≤ Module.finrank ℝ (LinearMap.ker T.mulVecLin) := Submodule.finrank_mono hmap

end LatticeSystem.Fermion
