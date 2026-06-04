import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki §11.3.4: general theory of flat-band ferromagnetism (Theorem 11.15)

This file sets up Mielke's general theory of flat-band ferromagnetism and states
**Theorem 11.15** as a documented `axiom`, faithfully following Tasaki's
presentation (the necessary-and-sufficient result is deep; its proof is deferred,
matching the policy for Theorem 11.8 / Lemma 11.9 / Theorem 11.13).

## Setting (Tasaki §11.3.4, pp. 409–412)
Let `Λ = Fin (M+1)` with single-electron space `h = (Fin (M+1) → ℂ)`.  Fix a hopping
matrix `T` with `Tᴴ = T` and `T ≥ 0` (`Matrix.PosSemidef`).  Let `h₀ = ker T`,
`D₀ = dim h₀ > 0`, and `P₀` the orthogonal projection matrix onto `h₀`.  Set
`Λ₀ = {x | (P₀)_{x,x} ≠ 0}`.  Consider the standard Hubbard model `Ĥ = Ĥ_hop(T) +
Ĥ_int(U)` with `U > 0`, at exact flat-band filling `N = D₀`.

## Theorem 11.15
The model exhibits saturated ferromagnetism (`N+1`-fold degenerate ground states
with `S_tot = N/2`) **iff** the `|Λ₀|×|Λ₀|` submatrix `((P₀)_{x,y})_{x,y∈Λ₀}` is
*irreducible* (not block-decomposable: there is no partition `Λ₀ = Λ₁ ⊔ Λ₂` into
nonempty parts with `(P₀)_{x,y} = 0` for all `x ∈ Λ₁`, `y ∈ Λ₂`).

`P₀` is built from mathlib's orthogonal projection: `T.toEuclideanLin` realises the
hopping matrix as an endomorphism of `EuclideanSpace ℂ (Fin (M+1))`, `starProjection`
onto its kernel is the self-adjoint projection, and `toMatrixOrthonormal` (in the
standard orthonormal basis) recovers its matrix.  Tasaki's *block-decomposability*
irreducibility is captured by `Matrix.IsIrreducible` applied to the real nonnegative
support matrix `Complex.normSq ((P₀)_{x,y})` on `Λ₀`: this is sound because `P₀` is
Hermitian (so the support pattern is symmetric, and strong connectivity of the
support quiver coincides with Tasaki's irreducibility).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, Theorem 11.15 (pp. 409–410).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

variable {M : ℕ} (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)

/-- The single-electron zero-energy space `h₀ = ker T`, realised as a submodule of
`EuclideanSpace ℂ (Fin (M+1))` via `Matrix.toEuclideanLin`. -/
noncomputable def generalFlatBandKernel : Submodule ℂ (EuclideanSpace ℂ (Fin (M + 1))) :=
  LinearMap.ker (Matrix.toEuclideanLin T)

/-- **`D₀ = dim h₀`** (Tasaki §11.3.4): the dimension of the single-electron flat
band (zero-energy space of the hopping matrix `T`). -/
noncomputable def generalFlatBandDim : ℕ :=
  Module.finrank ℂ (generalFlatBandKernel T)

/-- **The projection matrix `P₀`** onto the flat band `h₀ = ker T` (Tasaki §11.3.4):
the matrix, in the standard orthonormal basis, of the self-adjoint orthogonal
projection onto `ker T`. -/
noncomputable def generalFlatBandProjectionMatrix :
    Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin (M + 1)) ℂ)
    (generalFlatBandKernel T).starProjection.toLinearMap

/-- **The active sites `Λ₀ = {x | (P₀)_{x,x} ≠ 0}`** (Tasaki §11.3.4): the support of
the flat band's diagonal projection density. -/
def generalFlatBandActiveSites : Type :=
  { x : Fin (M + 1) // generalFlatBandProjectionMatrix T x x ≠ 0 }

/-- The real nonnegative **support matrix** of the restricted projection `((P₀)_{x,y})`
on `Λ₀`: `Complex.normSq` of each entry.  Its `Matrix.IsIrreducible` is equivalent to
Tasaki's block-decomposability irreducibility of `((P₀)_{x,y})_{x,y∈Λ₀}` (`P₀` Hermitian
⇒ symmetric support, so strong connectivity = irreducibility); mathlib's
`Matrix.IsIrreducible` is stated for entrywise-nonnegative matrices, hence this real form
rather than the complex projection directly. -/
noncomputable def generalFlatBandProjectionSupportMatrix :
    Matrix (generalFlatBandActiveSites T) (generalFlatBandActiveSites T) ℝ :=
  fun x y => Complex.normSq (generalFlatBandProjectionMatrix T x.1 y.1)

/-- **Tasaki's irreducibility condition for Theorem 11.15**: the `Λ₀ × Λ₀` projection
submatrix is irreducible (not block-decomposable). -/
def generalFlatBandProjectionIrreducible : Prop :=
  (generalFlatBandProjectionSupportMatrix T).IsIrreducible

/-- The zero-energy, fixed-`D₀`-electron ground subspace of the general flat-band
Hubbard model: `ker Ĥ` intersected with the `D₀`-electron number sector. -/
noncomputable def generalFlatBandGroundSubmodule (U : ℝ) :
    Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  LinearMap.ker (hubbardHamiltonian M T (U : ℂ)).mulVecLin ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * M + 1)).mulVecLin
      (generalFlatBandDim T : ℂ)

/-- **Saturated ferromagnetism at flat-band filling** `N = D₀` (the conclusion of
Theorem 11.15): the ground subspace is the `D₀ + 1 = 2S_max + 1`-fold multiplet, and
every ground state is an `(Ŝ_tot)²` eigenvector at `S_max(S_max + 1)`, `S_max = D₀/2`.
Mirrors the `mielke_theorem_11_13` ground-subspace formulation. -/
def generalFlatBandFerromagnetic (U : ℝ) : Prop :=
  Module.finrank ℂ (generalFlatBandGroundSubmodule T U) = generalFlatBandDim T + 1 ∧
    ∀ v ∈ generalFlatBandGroundSubmodule T U,
      (fermionTotalSpinSquared M).mulVec v =
        (((generalFlatBandDim T : ℂ) / 2) * ((generalFlatBandDim T : ℂ) / 2 + 1)) • v

/-- **Tasaki Theorem 11.15 (general flat-band ferromagnetism), AXIOM.**  For a Hermitian
positive-semidefinite hopping matrix `T` with nonempty flat band (`D₀ > 0`) and `U > 0`,
the `D₀`-electron Hubbard model is saturated-ferromagnetic **iff** the `Λ₀ × Λ₀`
projection submatrix is irreducible.  Tasaki gives a complete proof (via Lemma 11.16 and
Theorem 11.17); it is deep, so the statement is recorded here as a documented axiom (to be
discharged), matching the policy for Theorem 11.8 / Lemma 11.9 / Theorem 11.13. -/
axiom tasaki_theorem_11_15 (U : ℝ) (hT : T.PosSemidef)
    (hD0 : 0 < generalFlatBandDim T) (hU : 0 < U) :
    generalFlatBandFerromagnetic T U ↔ generalFlatBandProjectionIrreducible T

end LatticeSystem.Fermion
