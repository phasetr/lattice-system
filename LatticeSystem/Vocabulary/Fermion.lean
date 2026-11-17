module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Fermionic occupation-basis operators

An explicitly chosen order on the modes fixes the ascending occupation basis.
On a finite mode carrier, the full Fock coordinate space is
`EuclideanSpace ℂ (Finset M)`, including the empty occupation. A fixed-particle
sector uses occupations of the corresponding cardinality; creation and
annihilation are operators on the full space rather than that one sector.
-/

@[expose] public section

open scoped BigOperators

namespace LatticeSystem

/-- Creation matrix coefficients in the ascending occupation basis.

The sign counts occupied modes preceding the inserted mode. For finite `M`,
these coefficients represent the creation operator on the full Euclidean Fock
space used in Tasaki's (9.2.35)--(9.2.37). This raw coefficient definition makes
no assertion about a Hilbert completion for infinite `M`.
-/
noncomputable def fermionCreationAt {M : Type*} [LinearOrder M] (mode : M) :
    Matrix (Finset M) (Finset M) ℂ :=
  fun row column =>
    if mode ∈ column then 0
    else if row = insert mode column then (-1 : ℂ) ^ (column.filter (· < mode)).card
    else 0

/-- Annihilation matrix coefficients, conjugate-transpose to creation in the
chosen occupation basis. On a finite mode carrier the adjoint is with respect
to the Euclidean inner product; no fixed particle-number sector is its domain.
-/
noncomputable def fermionAnnihilationAt {M : Type*} [LinearOrder M] (mode : M) :
    Matrix (Finset M) (Finset M) ℂ :=
  (fermionCreationAt mode).conjTranspose

/-- The mode number operator, defined as creation times annihilation as in
Tasaki's (9.2.29), on the full finite-mode Fock coordinate space.
-/
noncomputable def fermionNumberAt {M : Type*} [Fintype M] [LinearOrder M] (mode : M) :
    Matrix (Finset M) (Finset M) ℂ :=
  fermionCreationAt mode * fermionAnnihilationAt mode

/-- Total particle number, the sum of all mode number operators in Tasaki's
(9.2.33). The vacuum sector remains part of the full finite-mode space.
-/
noncomputable def totalFermionNumber {M : Type*} [Fintype M] [LinearOrder M] :
    Matrix (Finset M) (Finset M) ℂ :=
  ∑ mode, fermionNumberAt mode

/-- Creation in an arbitrary one-particle vector, with the linear coefficients
of Tasaki's (9.2.46). No normalization of the input vector is assumed.
-/
noncomputable def fermionCreation {M : Type*} [Fintype M] [LinearOrder M]
    (φ : EuclideanSpace ℂ M) : Matrix (Finset M) (Finset M) ℂ :=
  ∑ mode, φ mode • fermionCreationAt mode

/-- Annihilation in an arbitrary one-particle vector, using the conjugated
coefficients of Tasaki's (9.2.46), without a normalization assumption.
-/
noncomputable def fermionAnnihilation {M : Type*} [Fintype M] [LinearOrder M]
    (φ : EuclideanSpace ℂ M) : Matrix (Finset M) (Finset M) ℂ :=
  ∑ mode, star (φ mode) • fermionAnnihilationAt mode

/-- Creation with fixed spin `σ` and spatial wave function `φ`, as in Tasaki's
(9.2.62). Spin labels `0` and `1` denote up and down. The supplied order on
`V × Fin 2` fixes the occupation basis; `φ` need not be normalized.
-/
noncomputable def spinFermionCreation {V : Type*} [Fintype V]
    [LinearOrder (V × Fin 2)] (σ : Fin 2) (φ : EuclideanSpace ℂ V) :
    Matrix (Finset (V × Fin 2)) (Finset (V × Fin 2)) ℂ :=
  ∑ site, φ site • fermionCreationAt (site, σ)

/-- Annihilation with fixed spin `σ` and spatial wave function `φ`, using the
conjugated coefficients of Tasaki's (9.2.62). It acts on the full occupation
space, includes the vacuum, and assumes no normalization of `φ`.
-/
noncomputable def spinFermionAnnihilation {V : Type*} [Fintype V]
    [LinearOrder (V × Fin 2)] (σ : Fin 2) (φ : EuclideanSpace ℂ V) :
    Matrix (Finset (V × Fin 2)) (Finset (V × Fin 2)) ℂ :=
  ∑ site, star (φ site) • fermionAnnihilationAt (site, σ)

end LatticeSystem
