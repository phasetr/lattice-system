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

Both theorems are **PROVED axiom-free**, each in its own downstream file:
`theorem_10_2_lieb_attractive_unique_singlet` (`LiebAttractiveTheorem102.lean`),
where Lieb's spin-space reflection-positivity is carried out on the balanced
(`Ŝ³ = 0`) block and lifted to the full `Ne`-electron sector through the
generic SU(2) multiplet engine (Tasaki Appendix A), and
`theorem_10_3_tian_pair_correlation_positive`
(`LiebAttractiveTheorem103.lean`). This file carries the shared definitional
layer both of them consume: the general hopping kinetic term reuses the
existing `hubbardKinetic`; the unique-ground-state predicate reuses
`IsUniqueGroundStateOn` from the degenerate-perturbation development.
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

/-- **The on-site pair creation and annihilation factors are mutually adjoint**,
`(ĉ†_{x,↑} ĉ†_{x,↓})ᴴ = ĉ_{x,↓} ĉ_{x,↑}`: the two halves of `hubbardPairCorrelationOp` at `x = y`,
and the per-site summands of the total pair operators of Theorem 10.8. -/
theorem fermionSitePairCreation_conjTranspose (N : ℕ) (x : Fin (N + 1)) :
    Matrix.conjTranspose (fermionUpCreation N x * fermionDownCreation N x)
      = fermionDownAnnihilation N x * fermionUpAnnihilation N x := by
  rw [Matrix.conjTranspose_mul, fermionDownCreation_conjTranspose,
    fermionUpCreation_conjTranspose]

/-- The expectation `⟨φ| O |φ⟩` of an observable `O` in a (Euclidean)
state vector `φ`. -/
noncomputable def euclideanExpectation {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) : ℂ :=
  dotProduct (star φ.ofLp) (O.mulVec φ.ofLp)

/-! ## Linearity and transport of the Euclidean expectation -/

/-- The Euclidean expectation is homogeneous in the observable. -/
theorem euclideanExpectation_smul (a : ℂ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (a • O) φ = a * euclideanExpectation O φ := by
  unfold euclideanExpectation
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The Euclidean expectation is additive in the observable. -/
theorem euclideanExpectation_add (O₁ O₂ : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (O₁ + O₂) φ
      = euclideanExpectation O₁ φ + euclideanExpectation O₂ φ := by
  unfold euclideanExpectation
  rw [Matrix.add_mulVec, dotProduct_add]

/-- The Euclidean expectation is additive over a `Finset` sum of observables,
`⟨φ| Σ_k O_k |φ⟩ = Σ_k ⟨φ| O_k |φ⟩`. -/
theorem euclideanExpectation_sum {κ : Type*} (s : Finset κ)
    (O : κ → ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (∑ k ∈ s, O k) φ = ∑ k ∈ s, euclideanExpectation (O k) φ := by
  unfold euclideanExpectation
  rw [Matrix.sum_mulVec, dotProduct_sum]

/-- **Shiba transport of the Euclidean expectation**: if `ψ = Û φ_attr` then
`⟨ψ| O |ψ⟩ = ⟨φ_attr| Ûᴴ O Û |φ_attr⟩`. -/
theorem euclideanExpectation_shiba_conj (O : ManyBodyOp (Fin (2 * N + 2)))
    (Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (ψ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = Ush.mulVec φattr.ofLp) :
    euclideanExpectation O ψ
      = euclideanExpectation (Matrix.conjTranspose Ush * O * Ush) φattr := by
  unfold euclideanExpectation
  rw [hψ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

/-- The Euclidean `⟨v| Aᴴ A |v⟩` is the (nonnegative real) squared norm of `A v`. -/
theorem euclideanExpectation_conjTranspose_mul_self
    (M : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (Matrix.conjTranspose M * M) φ
      = ((∑ j, Complex.normSq ((M.mulVec φ.ofLp) j) : ℝ) : ℂ) := by
  unfold euclideanExpectation
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

end LatticeSystem.Fermion
