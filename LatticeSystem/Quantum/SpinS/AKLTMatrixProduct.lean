import LatticeSystem.Quantum.SpinS.MPSTheorem76Unitary

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

**Theorem 7.6** (Fannes–Nachtergaele–Werner): if two injective collections have identical periodic
trace coefficients at every chain length, then there is a unitary `U`, unique up to phase, such
that `B^σ = U† A^σ U` for every `σ`. This uniqueness underlies the classification of
symmetry-protected topological phases (§8.3.4).

The transfer matrix, ordered products, normalization, spanning conditions, spectral primitivity
condition, and corrected Theorem 7.5 are imported from `MPSTheorem75`. Theorem 7.6 is proved from
the finite-dimensional algebra and unitary-gauge substrate in `MPSTheorem76Unitary`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.6, eqs. (7.2.43)–(7.2.44), p. 203; M. Fannes, B. Nachtergaele, and
R. F. Werner, “Finitely correlated pure states,” *Journal of Functional Analysis* **120** (1994),
511–534.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {D N : ℕ}

/-- **Tasaki Theorem 7.6 (uniqueness of the injective MPS representation).**
Two injective MPS collections with identical periodic trace coefficients at every length are
related by a unitary gauge, and that unitary is unique up to phase.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.6, eqs. (7.2.43)–(7.2.44), p. 203; M. Fannes, B. Nachtergaele, and
R. F. Werner, *Journal of Functional Analysis* **120** (1994), 511–534. -/
theorem mps_theorem_7_6
    (A B : MPSMatrices D N) (lamA lamB : ℝ)
    (hA : IsInjectiveMPS A lamA)
    (hB : IsInjectiveMPS B lamB)
    (hsame : GeneratesSameMPS A B) :
    ∃ U : Matrix (Fin D) (Fin D) ℂ,
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      (∀ σ, B σ = U.conjTranspose * A σ * U) ∧
      ∀ V : Matrix (Fin D) (Fin D) ℂ,
        V ∈ Matrix.unitaryGroup (Fin D) ℂ →
        (∀ σ, B σ = V.conjTranspose * A σ * V) →
        ∃ z : ℂ, ‖z‖ = 1 ∧ V = z • U := by
  obtain ⟨U, hgauge, hunique⟩ :=
    MPSTheorem76.Internal.exists_unitary_gauge_data A B lamA lamB hA hB hsame
  exact ⟨U, U.property, hgauge, hunique⟩

end LatticeSystem.Quantum
