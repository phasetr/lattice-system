import LatticeSystem.Quantum.SpinS.GeneralSOpenChainGroundSpace

/-!
# Ground space of the general-`S` open AKLT chain is the joint bond kernel

Regression gate for `Quantum.GeneralSOpenChainGroundSpace`: the zero-energy space
`openAKLTGroundSpaceGeneralS`, its identification with the kernel of the Hamiltonian's linear map,
positive semidefiniteness of the Hamiltonian, the frustration-free characterization
`mem_openAKLTGroundSpaceGeneralS_iff`, and the boundary shape it yields for the Weyl image of a
ground state (`weylMap_groundSpaceGeneralS_eq_boundary_mul_prod`).  This file pins the exact
signatures of those declarations.
-/

open Matrix MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open scoped ComplexOrder

namespace LatticeSystem.Tests.GeneralSOpenChainGroundSpace

/-- **Signature pin: the zero-energy space is the kernel of the Hamiltonian's linear map.** -/
example (L S : ℕ) :
    openAKLTGroundSpaceGeneralS L S
      = LinearMap.ker (Matrix.mulVecLin (openAKLTHamiltonianGeneralS L S)) :=
  openAKLTGroundSpaceGeneralS_eq_ker L S

/-- **Signature pin: `Ĥ ≥ 0`.** -/
example {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    (openAKLTHamiltonianGeneralS L S).PosSemidef :=
  openAKLTHamiltonianGeneralS_posSemidef hL hS

/-- **Signature pin, headline: the zero-energy space is the joint bond kernel.**  Instantiated at
`L = 2`, the shortest open chain (a single bond), with `S` left general. -/
example {S : ℕ} (hS : S ≠ 0) (Φ : (Fin 2 → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS 2 S
      ↔ ∀ x ∈ openBonds 2, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 :=
  mem_openAKLTGroundSpaceGeneralS_iff (by norm_num) hS Φ

/-- **General-`L` signature pin.** -/
example {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS L S
      ↔ ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 :=
  mem_openAKLTGroundSpaceGeneralS_iff hL hS Φ

/-- **Signature pin: boundary shape of the ground states.**  The Weyl image of a zero-energy state
is the product of the `S`-th powers of the open bond factors times a boundary form supported on the
`(S+1)²` boundary multidegrees of Tasaki §8.3.1, p. 252. -/
example {m S : ℕ} (hS : S ≠ 0) {Φ : (Fin (m + 2) → Fin (2 * S + 1)) → ℂ}
    (hΦ : Φ ∈ openAKLTGroundSpaceGeneralS (m + 2) S) :
    ∃ c : Fin (S + 1) × Fin (S + 1) → ℂ,
      weylMap Φ
        = (∑ ab : Fin (S + 1) × Fin (S + 1), monomial (boundaryDeg m S ab) (c ab))
            * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  weylMap_groundSpaceGeneralS_eq_boundary_mul_prod hS hΦ

end LatticeSystem.Tests.GeneralSOpenChainGroundSpace
