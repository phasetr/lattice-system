import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Lieb's theorem for the attractive Hubbard model (Tasaki §10.2.1, Theorems 10.2 & 10.3)

This file formalizes the statements of **Tasaki Theorem 10.2** (Lieb's
theorem for the attractive Hubbard model) and **Theorem 10.3** (Tian's
pair-correlation positivity), from Hal Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.1, pp. 348–349.

The attractive Hubbard model has Hamiltonian `Ĥ = Ĥhop + Ĥatt-int` with an
arbitrary real symmetric connected hopping matrix `T` (arbitrary on-site
energies allowed) and on-site attraction `Ĥatt-int = −Σ_x U_x n̂_{x,↑} n̂_{x,↓}`,
`U_x > 0` (eqs. (10.2.1)/(10.2.2)).

* **Theorem 10.2**: for even electron number `N` with `0 < N ≤ 2|Λ|`, the
  ground state is unique and has total spin `S_tot = 0`.
* **Theorem 10.3**: the pair-transfer correlation
  `⟨ΦGS| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |ΦGS⟩` is strictly positive
  (a measure of off-diagonal long-range order).

## Status

**Theorem 10.2 is now PROVED axiom-free** (in `LiebAttractiveTheorem102.lean`,
`theorem_10_2_lieb_attractive_unique_singlet`): Lieb's spin-space
reflection-positivity is carried out on the balanced (`Ŝ³ = 0`) block and
lifted to the full `Ne`-electron sector through the generic SU(2) multiplet
engine (Tasaki Appendix A). Theorem 10.3 (Tian's pair-correlation
positivity) is still recorded as a faithful documented `axiom`, built on a
concrete attractive Hubbard Hamiltonian. The general hopping kinetic term
reuses the existing `hubbardKinetic`; the unique-ground-state predicate
reuses `IsUniqueGroundStateOn` from the degenerate-perturbation development.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The support graph of a real hopping matrix `T`, with an edge between
distinct `x, y` whenever `T x y` or `T y x` is nonzero (diagonal on-site
energies `T x x` are ignored). Connectivity of this graph is Tasaki's
"`Λ` is connected through nonvanishing `t_{x,y}`" hypothesis. -/
def hoppingSupportGraph (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    SimpleGraph (Fin (N + 1)) :=
  SimpleGraph.fromRel (fun x y => T x y ≠ 0)

/-- The site-dependent on-site Hubbard interaction
`Σ_x U_x n̂_{x,↑} n̂_{x,↓}`. -/
noncomputable def hubbardOnSiteInteractionSite (N : ℕ)
    (U : Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), U x • (fermionUpNumber N x * fermionDownNumber N x)

/-- The attractive on-site interaction `−Σ_x U_x n̂_{x,↑} n̂_{x,↓}`
(Tasaki eq. (10.2.2)), with positive `U_x`. -/
noncomputable def attractiveHubbardInteraction (N : ℕ)
    (U : Fin (N + 1) → ℝ) : ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardOnSiteInteractionSite N (fun x => -(U x : ℂ))

/-- The **attractive Hubbard Hamiltonian** `Ĥ = Ĥhop + Ĥatt-int`
(Tasaki §10.2.1, eqs. (10.2.1)/(10.2.2)): general real symmetric hopping
`T` plus site-dependent on-site attraction `−Σ_x U_x n̂_{x,↑} n̂_{x,↓}`. -/
noncomputable def attractiveHubbardHamiltonian (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (fun x y => (T x y : ℂ)) + attractiveHubbardInteraction N U

/-- The fixed electron-number sector `H_N`, as a subspace of the
`EuclideanSpace` of computational configurations: the `(N : ℂ)`-eigenspace
of the total number operator. -/
noncomputable def electronNumberSectorEuclidean (N Ne : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :=
  Module.End.eigenspace
    (Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1))) (Ne : ℂ)

/-- The on-site pair-transfer operator
`ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑}` whose ground-state expectation measures
off-diagonal long-range order (Tasaki eq. (10.2.4)). -/
noncomputable def hubbardPairCorrelationOp (N : ℕ) (x y : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionUpCreation N x * fermionDownCreation N x *
    fermionDownAnnihilation N y * fermionUpAnnihilation N y

/-- The expectation `⟨φ| O |φ⟩` of an observable `O` in a (Euclidean)
state vector `φ`. -/
noncomputable def euclideanExpectation {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) : ℂ :=
  dotProduct (star φ.ofLp) (O.mulVec φ.ofLp)

-- **Tasaki Theorem 10.3** (Tian's pair-correlation positivity, 1st ed., Springer 2020, §10.2,
-- p. 349, eq. (10.2.4)) is now a **proved theorem** `theorem_10_3_tian_pair_correlation_positive`
-- in `LiebAttractiveTheorem103.lean` (no longer an axiom).

end LatticeSystem.Fermion
