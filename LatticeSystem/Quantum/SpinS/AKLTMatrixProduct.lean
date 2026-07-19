import LatticeSystem.Quantum.SpinS.MPSTheorem75
import LatticeSystem.Quantum.SpinS.MPSTheorem76Defs

/-!
# Tasaki §7.2.2: matrix product representation of the AKLT model (Theorems 7.5, 7.6)

The AKLT VBS ground state is the prototypical **matrix product state** (MPS): a collection of
`D × D` matrices `(A^σ)_{σ = −S,…,S}` builds the state `|Φ⟩ = Σ_σ tr(A^{σ_1} ⋯ A^{σ_L}) |σ⟩`.  Two
notions control its structure:

* the **transfer matrix** (eq. (7.2.42)) `Ã_{α,β;α',β'} = Σ_σ \overline{A^σ_{α,α'}} A^σ_{β,β'}`, a
  `D² × D²` matrix whose spectrum governs the correlations;
* **injectivity** (primitivity): the matrices are normalized,
  `Σ_σ A^σ (A^σ)† = λ I` (eq. (7.2.41), `λ > 0`), and satisfy the corrected faithful-dual
  spanning/spectral conditions formalized below.

**Printed Theorem 7.5** (injective matrix product states) claims that normalization alone makes
the following conditions equivalent: (i) the ordered products span all `D × D` matrices at some
length; (ii) they span at every sufficiently large length; (iii) `λ` is a nondegenerate transfer
eigenvalue and every other eigenvalue has strictly smaller modulus. This claim is false. The
corrected formalization additionally assumes `HasFaithfulDualEigenmatrix`. See `MPSTheorem75`,
`docs/index.md`, and `tex/proof-guide.tex` for the counterexample and the corrected statement.

**Theorem 7.6** (Fannes–Nachtergaele–Werner, stated without proof in the book): the injective matrix
product *representation* is essentially unique — two injective collections generating the same MPS
are related by a gauge `A^σ = (θ/c) U B^σ U†` with `U` unitary and `|θ| = 1`.  This uniqueness
underlies the classification of symmetry-protected topological phases (§8.3.4).

The transfer matrix, ordered products, normalization, spanning conditions, spectral primitivity
condition, and corrected Theorem 7.5 are imported from `MPSTheorem75`. Theorem 7.6, which is
unproven in the book, remains a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorems 7.5–7.6, eqs. (7.2.36), (7.2.41)–(7.2.42), pp. 202–203; M. Fannes, B.
Nachtergaele, R. F. Werner, Commun. Math. Phys. **144**, 443 (1992).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {D N : ℕ}

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
