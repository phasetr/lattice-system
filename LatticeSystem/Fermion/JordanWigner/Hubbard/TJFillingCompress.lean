import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOperatorLift
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Tasaki 11.5: the `W = (N̂=Ne) ∩ H^hc` projection and embedding (Prop 11.24 PR-E2 ≥)

Toward the `W`-restricted A.17: this file sets up the orthonormal embedding of the filling space
`W = (N̂ = Ne) ∩ H^hc` into the full spinful Fock space, and the resolution-of-identity / projection
fact `T Tᴴ = id` on `W` (`tJFillingProjection_mulVec_eq_of_mem`), which drives the compression
homomorphism `compress(A) compress(B) = compress(A B)` for `W`-preserving operators.

`PreservesTJFillingW B` (`B` maps `W` into itself) is the reusable hypothesis: it holds for `Ĥ_tJ`
(`[Ĥ_tJ, N̂] = 0` + hard-core preservation) and will hold for the spin operators `Ŝ^α`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- The embedding of the filling space into the full Fock space: its column at the filling site-state
`s` is the computational basis vector `|Φ_s⟩ = basisVec (tJConfigOf s)`. -/
noncomputable def tJFillingEmbedding (N Ne : ℕ) :
    Matrix (Fin (2 * N + 2) → Fin 2) (TJFillingSector N Ne) ℂ :=
  Matrix.of (fun w s => basisVec (tJConfigOf N s.val) w)

/-- The filling space `W = (N̂ = Ne)`-eigenspace `⊓` the no-double-occupancy subspace. -/
noncomputable def tJFillingWSubmodule (N Ne : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ) ⊓
    hubbardHardcoreSubspace N

/-- Membership in `W`: an `N̂ = Ne` eigenvector lying in the hard-core subspace. -/
theorem mem_tJFillingWSubmodule_iff (Ne : ℕ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ} :
    v ∈ tJFillingWSubmodule N Ne ↔
      (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v ∧
        v ∈ hubbardHardcoreSubspace N := by
  rw [tJFillingWSubmodule, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  rfl

/-- **`B` preserves the filling space `W`.** The reusable hypothesis of the compression
homomorphism: `B` maps every `W`-vector into `W`. -/
def PreservesTJFillingW (N Ne : ℕ) (B : ManyBodyOp (Fin (2 * N + 2))) : Prop :=
  ∀ v ∈ tJFillingWSubmodule N Ne, B.mulVec v ∈ tJFillingWSubmodule N Ne

/-- `T` maps a filling coefficient vector to its filling expansion: `T u = Σ_s u_s |Φ_s⟩`. -/
theorem tJFillingEmbedding_mulVec (Ne : ℕ) (u : TJFillingSector N Ne → ℂ) :
    (tJFillingEmbedding N Ne).mulVec u = tJFillingExpansion N Ne u := by
  funext w
  unfold tJFillingEmbedding tJFillingExpansion
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun s _ => by rw [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_comm])

/-- `Tᴴ` maps a Fock vector to its filling coefficient functional: `(Tᴴ v)_s = ⟨Φ_s, v⟩`. -/
theorem tJFillingEmbedding_conjTranspose_mulVec (Ne : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (tJFillingEmbedding N Ne)ᴴ.mulVec v = tJFillingExpansionCoeff N Ne v := by
  funext s
  unfold tJFillingExpansionCoeff
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Matrix.conjTranspose_apply, tJFillingEmbedding, Matrix.of_apply]
  rw [show star (basisVec (tJConfigOf N s.val) w) = basisVec (tJConfigOf N s.val) w from by
    rw [basisVec_apply]; split <;> simp]

/-- **Projection identity.** `T Tᴴ` acts as the identity on the filling space `W`:
`T Tᴴ v = v` for `v ∈ W` (the resolution of identity over the orthonormal filling basis). -/
theorem tJFillingProjection_mulVec_eq_of_mem (Ne : ℕ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (h : v ∈ tJFillingWSubmodule N Ne) :
    (tJFillingEmbedding N Ne * (tJFillingEmbedding N Ne)ᴴ).mulVec v = v := by
  rw [← Matrix.mulVec_mulVec, tJFillingEmbedding_conjTranspose_mulVec, tJFillingEmbedding_mulVec]
  rw [mem_tJFillingWSubmodule_iff] at h
  exact (tJ_filling_completeness Ne v h.2 h.1).symm

/-- **`Ĥ_tJ` preserves the filling space `W`** (it conserves `N̂` and the hard-core constraint). -/
theorem preservesTJFillingW_tJHamiltonian (Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    PreservesTJFillingW N Ne (tJHamiltonian N G τ J) := by
  intro v hv
  rw [mem_tJFillingWSubmodule_iff] at hv ⊢
  exact ⟨tJHamiltonian_mulVec_preserves_number G τ J v (Ne : ℂ) hv.1,
    tJHamiltonian_mulVec_mem_hardcore G τ J hv.2⟩

/-- **The `W`-compression** `compress(A) = Tᴴ A T`: the matrix of `A` in the filling basis. -/
noncomputable def tJFillingCompress (N Ne : ℕ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    Matrix (TJFillingSector N Ne) (TJFillingSector N Ne) ℂ :=
  (tJFillingEmbedding N Ne)ᴴ * A * tJFillingEmbedding N Ne

/-- A filling basis vector lies in `W`. -/
theorem basisVec_tJConfigOf_mem_tJFillingWSubmodule (Ne : ℕ) (s : TJFillingSector N Ne) :
    basisVec (tJConfigOf N s.val) ∈ tJFillingWSubmodule N Ne := by
  rw [mem_tJFillingWSubmodule_iff]
  exact ⟨fermionTotalNumber_mulVec_tJConfigOf_eq N s.val Ne s.property,
    tJConfigOf_mem_hardcore N s.val⟩

/-- The projection `T Tᴴ` fixes `B T` when `B` preserves `W` (each column `B |Φ_s⟩ ∈ W`). -/
theorem tJFillingProjection_mul_of_preserves (Ne : ℕ) {B : ManyBodyOp (Fin (2 * N + 2))}
    (hB : PreservesTJFillingW N Ne B) :
    (tJFillingEmbedding N Ne * (tJFillingEmbedding N Ne)ᴴ) * (B * tJFillingEmbedding N Ne)
      = B * tJFillingEmbedding N Ne := by
  ext w s
  have hcol : (fun x => (B * tJFillingEmbedding N Ne) x s)
      = B.mulVec (basisVec (tJConfigOf N s.val)) := by
    funext x; rw [Matrix.mul_apply]; rfl
  have hmem : B.mulVec (basisVec (tJConfigOf N s.val)) ∈ tJFillingWSubmodule N Ne :=
    hB _ (basisVec_tJConfigOf_mem_tJFillingWSubmodule Ne s)
  rw [Matrix.mul_apply,
    show (∑ x, (tJFillingEmbedding N Ne * (tJFillingEmbedding N Ne)ᴴ) w x *
          (B * tJFillingEmbedding N Ne) x s)
        = ((tJFillingEmbedding N Ne * (tJFillingEmbedding N Ne)ᴴ).mulVec
            (B.mulVec (basisVec (tJConfigOf N s.val)))) w from by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun x _ => by rw [congrFun hcol x]),
    tJFillingProjection_mulVec_eq_of_mem Ne hmem, ← congrFun hcol w]

/-- **Compression homomorphism.** `compress(A) compress(B) = compress(A B)` when `B` preserves the
filling space `W` (so the intermediate projection `T Tᴴ` between `A` and `B` is invisible). -/
theorem tJFillingCompress_mul_of_right_preserves (Ne : ℕ) (A : ManyBodyOp (Fin (2 * N + 2)))
    {B : ManyBodyOp (Fin (2 * N + 2))} (hB : PreservesTJFillingW N Ne B) :
    tJFillingCompress N Ne A * tJFillingCompress N Ne B = tJFillingCompress N Ne (A * B) := by
  unfold tJFillingCompress
  rw [show (tJFillingEmbedding N Ne)ᴴ * A * tJFillingEmbedding N Ne *
        ((tJFillingEmbedding N Ne)ᴴ * B * tJFillingEmbedding N Ne)
      = (tJFillingEmbedding N Ne)ᴴ * A *
          ((tJFillingEmbedding N Ne * (tJFillingEmbedding N Ne)ᴴ) *
            (B * tJFillingEmbedding N Ne)) by
      simp only [Matrix.mul_assoc],
    tJFillingProjection_mul_of_preserves Ne hB]
  simp only [Matrix.mul_assoc]

end LatticeSystem.Fermion
