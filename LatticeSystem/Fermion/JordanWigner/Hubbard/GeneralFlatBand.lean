import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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

/-- A vector lies in the flat band `h₀ = ker T` iff `T` annihilates it as a plain `mulVec`
(the `EuclideanSpace`/`L²` wrapping is transparent). -/
theorem generalFlatBand_mem_kernel_iff (v : EuclideanSpace ℂ (Fin (M + 1))) :
    v ∈ generalFlatBandKernel T ↔ T.mulVec (WithLp.ofLp v) = 0 := by
  rw [generalFlatBandKernel, LinearMap.mem_ker, Matrix.toLpLin_apply]
  constructor
  · intro h; have := congrArg WithLp.ofLp h; simpa using this
  · intro h; rw [h]; rfl

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
Expressed via the shared `IsMaximalSpinMultipletSubmodule` predicate (see
`mielke_theorem_11_13`). -/
def generalFlatBandFerromagnetic (U : ℝ) : Prop :=
  IsMaximalSpinMultipletSubmodule M (generalFlatBandGroundSubmodule T U) (generalFlatBandDim T)

/-- **Tasaki Theorem 11.15 (general flat-band ferromagnetism), AXIOM.**  For a Hermitian
positive-semidefinite hopping matrix `T` with nonempty flat band (`D₀ > 0`) and `U > 0`,
the `D₀`-electron Hubbard model is saturated-ferromagnetic **iff** the `Λ₀ × Λ₀`
projection submatrix is irreducible.  Tasaki gives a complete proof (via Lemma 11.16 and
Theorem 11.17); it is deep, so the statement is recorded here as a documented axiom (to be
discharged), matching the policy for Theorem 11.8 / Lemma 11.9 / Theorem 11.13. -/
axiom tasaki_theorem_11_15 (U : ℝ) (hT : T.PosSemidef)
    (hD0 : 0 < generalFlatBandDim T) (hU : 0 < U) :
    generalFlatBandFerromagnetic T U ↔ generalFlatBandProjectionIrreducible T

/-! ### Lemma 11.16 and Theorem 11.17 (the special basis and its connectivity)

Tasaki's proof of Theorem 11.15 proceeds through a *special basis* of the flat band
`h₀` (Lemma 11.16) and an equivalent connectivity condition on that basis
(Theorem 11.17).  Both are recorded here as documented axioms (Issue #4186). -/

/-- **Lemma 11.16 special-basis property**: `I ⊆ Λ` with `|I| = D₀` indexes a basis
`{μ_z}_{z∈I}` of the flat band `ker T` (`T.mulVec (μ z) = 0`, linearly independent and of
the right cardinality) which is *site-localised at the index*: `μ_z(z) ≠ 0` while
`μ_z(z') = 0` for every other index `z' ∈ I\{z}`. -/
def IsGeneralFlatBandSpecialBasis (I : Finset (Fin (M + 1)))
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) : Prop :=
  I.card = generalFlatBandDim T ∧
    (∀ z ∈ I, T.mulVec (μ z) = 0) ∧
    LinearIndependent ℂ (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)) ∧
    (∀ z ∈ I, μ z z ≠ 0) ∧
    (∀ z ∈ I, ∀ z' ∈ I, z ≠ z' → μ z z' = 0)

/-- **Lemma 11.16 (special basis of a flat band), AXIOM.**  For a Hermitian
positive-semidefinite `T`, the flat band `ker T` admits an index set `I` (`|I| = D₀`)
and a basis `{μ_z}` localised at the indices.  Tasaki proves this by elementary
determinantal-rank linear algebra; recorded as a documented axiom (to be discharged). -/
axiom generalFlatBand_lemma_11_16 (hT : T.PosSemidef) :
    ∃ (I : Finset (Fin (M + 1))) (μ : Fin (M + 1) → Fin (M + 1) → ℂ),
      IsGeneralFlatBandSpecialBasis T I μ

/-- The **connectivity graph of a special basis** (Tasaki §11.3.4, before Theorem 11.17):
two index sites `z, z'` are *directly connected* (`μ_z ∼ μ_{z'}`) iff they are distinct
and their basis vectors share a nonzero component. -/
def generalFlatBandBasisGraph (I : Finset (Fin (M + 1)))
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) : SimpleGraph I where
  Adj z z' := z.1 ≠ z'.1 ∧ ∃ x, μ z.1 x ≠ 0 ∧ μ z'.1 x ≠ 0
  symm := fun _ _ ⟨hne, x, h1, h2⟩ => ⟨hne.symm, x, h2, h1⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- **Tasaki's connectivity condition for Theorem 11.17**: the special basis `{μ_z}` is
connected (its connectivity graph is connected). -/
def generalFlatBandBasisConnected (I : Finset (Fin (M + 1)))
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) : Prop :=
  (generalFlatBandBasisGraph I μ).Connected

/-- **Tasaki Theorem 11.17 (connectivity form of flat-band ferromagnetism), AXIOM.**  For a
special basis `{μ_z}` of the flat band (Lemma 11.16), the `D₀`-electron Hubbard model is
saturated-ferromagnetic **iff** the basis is connected.  This is Mielke's second
necessary-and-sufficient condition; Tasaki shows its connectivity is independent of the
choice of special basis and equivalent to the irreducibility condition of Theorem 11.15.
Recorded as a documented axiom (Issue #4186), matching the Theorem 11.8 / 11.13 / 11.15
policy. -/
axiom generalFlatBand_theorem_11_17 (U : ℝ) (hT : T.PosSemidef)
    (hD0 : 0 < generalFlatBandDim T) (hU : 0 < U)
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ) :
    generalFlatBandFerromagnetic T U ↔ generalFlatBandBasisConnected I μ

end LatticeSystem.Fermion
