import LatticeSystem.Quantum.SpinS.AKLT

/-!
# Tasaki §7.2.2: matrix product representation of the AKLT model (Theorems 7.5, 7.6)

The AKLT VBS ground state is the prototypical **matrix product state** (MPS): a collection of
`D × D` matrices `(A^σ)_{σ = −S,…,S}` builds the state `|Φ⟩ = Σ_σ tr(A^{σ_1} ⋯ A^{σ_L}) |σ⟩`.  Two
notions control its structure:

* the **transfer matrix** (eq. (7.2.42)) `Ã_{α,β;α',β'} = Σ_σ \overline{A^σ_{α,α'}} A^σ_{β,β'}`, a
  `D² × D²` matrix whose spectrum governs the correlations;
* **injectivity** (primitivity): the matrices are normalized, `Σ_σ A^σ (A^σ)† = λ I` (eq. (7.2.41),
  `λ > 0`), and satisfy the equivalent spanning/spectral conditions of Theorem 7.5.

**Theorem 7.5** (injective matrix product states): for normalized `(A^σ)`, the following are
equivalent — (i) the ordered products `A^{σ_1} ⋯ A^{σ_{ℓ₀}}` span all `D × D` matrices for some
`ℓ₀`; (ii) they span for every `ℓ ≥ ℓ₀`; (iii) `λ` is a nondegenerate eigenvalue of the transfer
matrix `Ã` and every other eigenvalue is strictly smaller in modulus.  Injectivity implies
exponentially decaying correlations (no macroscopic superposition).

**Theorem 7.6** (Fannes–Nachtergaele–Werner, stated without proof in the book): the injective matrix
product *representation* is essentially unique — two injective collections generating the same MPS
are related by a gauge `A^σ = (θ/c) U B^σ U†` with `U` unitary and `|θ| = 1`.  This uniqueness
underlies the classification of symmetry-protected topological phases (§8.3.4).

The transfer matrix, the ordered products, the normalization, the spanning conditions, and the
spectral primitivity condition (iii) are all *defined concretely* here.  Theorem 7.5 (whose proof is
Perron–Frobenius theory for the completely positive transfer map) and Theorem 7.6 (unproven in the
book) are recorded as documented axioms.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorems 7.5–7.6, eqs. (7.2.36), (7.2.41)–(7.2.42), pp. 202–203; M. Fannes, B.
Nachtergaele, R. F. Werner, Commun. Math. Phys. **144**, 443 (1992).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {D N : ℕ}

/-- A collection of MPS matrices `(A^σ)_{σ = 0,…,N}` of bond dimension `D` for a spin-`S` site
(`N = 2S`): each `A^σ` is a `D × D` complex matrix. -/
abbrev MPSMatrices (D N : ℕ) : Type :=
  Fin (N + 1) → Matrix (Fin D) (Fin D) ℂ

/-- The **transfer matrix** `Ã` of an MPS (eq. (7.2.42)): the `D² × D²` matrix with entries
`Ã_{(α,β),(α',β')} = Σ_σ \overline{A^σ_{α,α'}} A^σ_{β,β'}`.  Its spectrum controls the decay of
correlations in the matrix product state. -/
noncomputable def mpsTransferMatrix (A : MPSMatrices D N) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ σ : Fin (N + 1), star (A σ p.1 q.1) * A σ p.2 q.2

/-- The **ordered product** `A^{σ_1} A^{σ_2} ⋯ A^{σ_ℓ}` of MPS matrices along a list of spin labels
(left-to-right matrix multiplication; the empty list gives the identity). -/
noncomputable def orderedProd (A : MPSMatrices D N) :
    List (Fin (N + 1)) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | σ :: ss => A σ * orderedProd A ss

/-- The MPS matrices **span at length `ℓ`**: the ordered products `A^{σ_1} ⋯ A^{σ_ℓ}` over all spin
sequences of length `ℓ` span the whole space of `D × D` matrices (condition behind Theorem 7.5(i),
(ii)). -/
def mpsProductsSpanAt (A : MPSMatrices D N) (ℓ : ℕ) : Prop :=
  Submodule.span ℂ {M : Matrix (Fin D) (Fin D) ℂ |
    ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ M = orderedProd A σs} = ⊤

/-- **Normalization (eq. (7.2.41))** `Σ_σ A^σ (A^σ)† = λ I` for a positive real `λ`. -/
def IsMPSNormalized (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  0 < lam ∧
    (∑ σ : Fin (N + 1), A σ * (A σ).conjTranspose) = (lam : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)

/-- **Theorem 7.5(i)**: the ordered products span all `D × D` matrices at *some* length `ℓ₀`. -/
def MPSSpansEventually (A : MPSMatrices D N) : Prop :=
  ∃ ℓ₀ : ℕ, mpsProductsSpanAt A ℓ₀

/-- **Theorem 7.5(ii)**: the ordered products span all `D × D` matrices at *every* length `ℓ ≥ ℓ₀`
for some `ℓ₀`. -/
def MPSSpansForAllLarge (A : MPSMatrices D N) : Prop :=
  ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → mpsProductsSpanAt A ℓ

/-- **Theorem 7.5(iii): primitive transfer spectrum.**  `λ` is a nondegenerate eigenvalue of the
transfer matrix `Ã` (its eigenspace is one-dimensional) and every other eigenvalue is strictly
smaller in modulus, `|λ_j| < λ`.  This is the spectral-gap condition characterizing an injective
(primitive) MPS. -/
noncomputable def HasPrimitiveTransferSpectrum (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  (lam : ℂ) ∈ spectrum ℂ (mpsTransferMatrix A) ∧
    finrank ℂ (LinearMap.ker
      ((mpsTransferMatrix A).mulVecLin - (lam : ℂ) • LinearMap.id)) = 1 ∧
    ∀ μ : ℂ, μ ∈ spectrum ℂ (mpsTransferMatrix A) → μ ≠ (lam : ℂ) → ‖μ‖ < lam

/-- A collection of MPS matrices is **injective (primitive)** if it is normalized (eq. (7.2.41)) and
satisfies the three equivalent conditions of Theorem 7.5. -/
def IsInjectiveMPS (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  IsMPSNormalized A lam ∧ MPSSpansEventually A ∧ MPSSpansForAllLarge A ∧
    HasPrimitiveTransferSpectrum A lam

/-- **Tasaki Theorem 7.5 (injective matrix product states), AXIOM.**  For a normalized collection of
MPS matrices (eq. (7.2.41), `λ > 0`) of positive bond dimension, the three conditions are
equivalent:
(i) the ordered products span all `D × D` matrices at some length (`MPSSpansEventually`); (ii) they
span at every sufficiently large length (`MPSSpansForAllLarge`); (iii) `λ` is a nondegenerate
top eigenvalue of the transfer matrix with a spectral gap (`HasPrimitiveTransferSpectrum`).  The
proof is Perron–Frobenius theory for the completely positive transfer map; recorded as a documented
axiom. -/
axiom mps_theorem_7_5 (A : MPSMatrices D N) (lam : ℝ) (hD : 0 < D)
    (hnorm : IsMPSNormalized A lam) :
    (MPSSpansEventually A ↔ MPSSpansForAllLarge A) ∧
      (MPSSpansForAllLarge A ↔ HasPrimitiveTransferSpectrum A lam)

/-- Two MPS matrix collections **generate the same matrix product state** (eq. (7.2.36) for all
chain lengths and boundary conditions).  A faithful definition needs the explicit MPS state
vectors; it is kept as an uninterpreted predicate so the uniqueness theorem applies only to
genuinely equal
states. -/
axiom GeneratesSameMPS (A B : MPSMatrices D N) : Prop

/-- **Tasaki Theorem 7.6 (uniqueness of the injective MPS representation,
Fannes–Nachtergaele–Werner), AXIOM.**  Two injective collections `(A^σ)`, `(B^σ)` that generate the
same matrix product state are
related by a **unitary gauge transformation**: there is a unitary `U` such that `A^σ = U B^σ U†` for
every `σ` (eq. (7.2.44); no additional rescaling — a nonzero scalar would multiply the length-`L`
amplitudes by its `L`-th power and so change the state).  The injective matrix product
representation is therefore essentially unique (up to unitary gauge), the fact underlying the
classification of symmetry-protected topological phases (§8.3.4).  Stated without proof in the book;
recorded as a
documented axiom. -/
axiom mps_theorem_7_6 (A B : MPSMatrices D N) (lamA lamB : ℝ)
    (hA : IsInjectiveMPS A lamA) (hB : IsInjectiveMPS B lamB) (hsame : GeneratesSameMPS A B) :
    ∃ U : Matrix (Fin D) (Fin D) ℂ,
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        ∀ σ : Fin (N + 1), A σ = U * B σ * U.conjTranspose

end LatticeSystem.Quantum
