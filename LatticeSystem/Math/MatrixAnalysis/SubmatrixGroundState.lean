import LatticeSystem.Math.MatrixAnalysis.BlockTransport
import LatticeSystem.Math.SubmoduleFinrankLeOne

/-!
# Ground-state transport across reindexing, constant shifts, and `finrank ≤ 1`

Generic (model-independent) ground-state infrastructure needed for the Theorem 10.4 (Lieb
repulsive Hubbard half-filling) discharge arc, PR-11a
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.2). This complements `BlockTransport.lean`'s coordinate-block transport with three further
generic facts about `IsUniqueGroundStateOn` (`Math/MatrixAnalysis/DegeneratePerturbation.lean`):
reindexing along an `Equiv`, real constant shifts, and the promotion of an eigenspace `finrank ≤ 1`
bound plus energy minimality to a genuine unique-ground-state witness. It also states the
eigenspace analogue of `BlockTransport.lean`'s `matrixKernel_diagonal_eq_coordinateSpan` and the
downward-restriction (`mono`) lemma for `IsUniqueGroundStateOn` along a submodule inclusion.

**Status: Red (PR-11a).** Every declaration below is a type signature only (`sorry`); no proof is
supplied in this file yet. `dev-implement` discharges the `sorry`s in the same declared shapes.

## Main results (stated, not yet proved)

* `isUniqueGroundStateOn_reindex_iff` — `IsUniqueGroundStateOn ⊤ H E φ` transports along an index
  `Equiv e : n ≃ m` to `IsUniqueGroundStateOn ⊤ (H.submatrix e e) E (φ ∘ e)` (up to the coordinate
  reindexing of the candidate vector).
* `isUniqueGroundStateOn_sub_smul_one_iff` — shifting `H` by a real constant multiple of the
  identity shifts the ground energy by the same constant and preserves the ground state and
  ground-space predicate.
* `isUniqueGroundStateOn_of_finrank_eigenspace_le_one` — from `finrank ≤ 1` of the `E`-eigenspace
  of `H` (as a `Module.End` on the ambient Pi type via `Matrix.toLin'`), a nonzero `E`-eigenvector,
  and eigenvalue-minimality among all real eigenvalues of `H`, constructs a normalized
  `IsUniqueGroundStateOn ⊤ H E` witness. Reuses `exists_smul_of_mem_of_finrank_le_one`
  (`Math/SubmoduleFinrankLeOne.lean`) rather than re-deriving scalar dependence.
* `secondOrderEffectiveHamiltonian_eq_kernelProjectionMatrix_conj` — the second-order effective
  Hamiltonian is sandwiched by the kernel projection of `H0`,
  `Ĥeff = P̂₀ · Ĥeff · P̂₀`, a consequence of idempotence of `kernelProjectionMatrix`.
* `eigenspace_diagonal_eq_coordinateSpan` — the eigenspace analogue of
  `matrixKernel_diagonal_eq_coordinateSpan` (`BlockTransport.lean`): the `L`-eigenspace of a
  diagonal matrix equals the coordinate span of the predicate characterizing entries equal to `L`.
* `IsUniqueGroundStateOn.mono` — `IsUniqueGroundStateOn` restricts downward along a submodule
  inclusion `K ≤ K'`, given the candidate lies in the smaller submodule.
-/

namespace LatticeSystem.Math

open Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Reindexing transport of `IsUniqueGroundStateOn`.** For an index equivalence `e : n ≃ m`,
`H` has `φ` as its unique ground state on `⊤` over `n` iff the `e`-submatrix of `H` has the
`e`-reindexed candidate as its unique ground state on `⊤` over `m`. -/
theorem isUniqueGroundStateOn_reindex_iff (H : Matrix n n ℂ) (e : n ≃ m) (E : ℝ)
    (φ : EuclideanSpace ℂ n) :
    IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) H E φ ↔
      IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ m))
        (H.submatrix e.symm e.symm) E (WithLp.toLp 2 (fun j => (WithLp.ofLp φ) (e.symm j))) := by
  sorry

/-- **Real constant shift preserves unique-ground-state transport.** Shifting `H` by `(a : ℂ) • 1`
shifts the ground energy by `a` and leaves the ground submodule, candidate, and uniqueness clause
unchanged: `IsUniqueGroundStateOn K H E φ ↔ IsUniqueGroundStateOn K (H - (a : ℂ) • 1) (E - a) φ`. -/
theorem isUniqueGroundStateOn_sub_smul_one_iff (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (a : ℝ) (E : ℝ) (φ : EuclideanSpace ℂ n) :
    IsUniqueGroundStateOn K H E φ ↔
      IsUniqueGroundStateOn K (H - (a : ℂ) • (1 : Matrix n n ℂ)) (E - a) φ := by
  sorry

/-- **From `finrank ≤ 1` and minimality to a unique ground state.** If the `E`-eigenspace of `H`
(as a `Module.End` on the Pi type `n → ℂ` via `Matrix.toLin'`) has `finrank ≤ 1`, `x : n → ℂ` is a
nonzero vector of that eigenspace, and `E` is `≤` every real eigenvalue of `H` (witnessed by a
nonzero `Matrix.toLin'`-eigenvector), then the `EuclideanSpace`-normalization of `x` is `H`'s
unique ground state on `⊤`. -/
theorem isUniqueGroundStateOn_of_finrank_eigenspace_le_one (H : Matrix n n ℂ) (E : ℝ)
    (x : n → ℂ)
    (hx_mem : x ∈ Module.End.eigenspace (Matrix.toLin' H) (E : ℂ))
    (hx0 : x ≠ 0)
    (hfin : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) (E : ℂ)) ≤ 1)
    (hmin : ∀ μ : ℝ, (∃ y : n → ℂ, y ≠ 0 ∧ Matrix.toLin' H y = (μ : ℂ) • y) → E ≤ μ) :
    IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) H E
      ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖⁻¹ : ℂ) • (WithLp.toLp 2 x : EuclideanSpace ℂ n)) := by
  sorry

/-- **The second-order effective Hamiltonian is block-diagonal on the kernel of `H0`.**
`secondOrderEffectiveHamiltonian H0 V H0inv = P̂₀ · secondOrderEffectiveHamiltonian H0 V H0inv · P̂₀`,
where `P̂₀ = kernelProjectionMatrix H0`; a direct consequence of idempotence of
`kernelProjectionMatrix`, supplying the `hblock` hypothesis of
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix` for `Ĥeff` generically (once `P̂₀` is
identified with a coordinate-block indicator via `matrixKernel_diagonal_eq_coordinateSpan`). -/
theorem secondOrderEffectiveHamiltonian_eq_kernelProjectionMatrix_conj
    (H0 V H0inv : Matrix n n ℂ) :
    secondOrderEffectiveHamiltonian H0 V H0inv
      = kernelProjectionMatrix H0 * secondOrderEffectiveHamiltonian H0 V H0inv
        * kernelProjectionMatrix H0 := by
  sorry

/-- **The eigenspace analogue of `matrixKernel_diagonal_eq_coordinateSpan`.** If a diagonal
matrix's entries equal `L` exactly on a decidable predicate `P`, its `L`-eigenspace (as a subspace
of `EuclideanSpace ℂ n`) is the coordinate span of `P`. -/
theorem eigenspace_diagonal_eq_coordinateSpan (d : n → ℂ) (L : ℂ) (P : n → Prop) [DecidablePred P]
    (hP : ∀ i, d i = L ↔ P i) :
    Module.End.eigenspace (Matrix.toEuclideanLin (Matrix.diagonal d)) L = coordinateSpan P := by
  sorry

/-- **`IsUniqueGroundStateOn` restricts downward along a submodule inclusion.** If `H` has a
unique ground state `φ` on a submodule `K'`, and `φ` lies in a smaller submodule `K ≤ K'`, then
`φ` is also the unique ground state of `H` on `K`. -/
theorem IsUniqueGroundStateOn.mono {K K' : Submodule ℂ (EuclideanSpace ℂ n)} (hKK' : K ≤ K')
    {H : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n} (hφK : φ ∈ K)
    (hGS : IsUniqueGroundStateOn K' H E φ) : IsUniqueGroundStateOn K H E φ := by
  sorry

end LatticeSystem.Math
