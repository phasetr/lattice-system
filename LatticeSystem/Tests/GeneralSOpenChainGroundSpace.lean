import LatticeSystem.Quantum.SpinS.GeneralSOpenChainGroundSpace

/-!
# Ground space of the general-`S` open AKLT chain is the joint bond kernel (PR-4b of #5292)

Regression gate for `Quantum.GeneralSOpenChainGroundSpace`: the zero-energy space
`openAKLTGroundSpaceGeneralS`, its identification with the kernel of the Hamiltonian's linear map,
positive semidefiniteness of the Hamiltonian, and the frustration-free characterization
`mem_openAKLTGroundSpaceGeneralS_iff`.  Every production declaration exercised below is currently
a `sorry` stub (dev-implement fills the proofs); this file pins the exact signatures.
-/

open Matrix LatticeSystem.Quantum LatticeSystem.Math
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
`L = 2` (the shortest open chain, a single bond) and `S = 1` so the site-state type matches the
pre-existing spin-one model (`Fin 3`). -/
example {S : ℕ} (hS : S ≠ 0) (Φ : (Fin 2 → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS 2 S
      ↔ ∀ x ∈ openBonds 2, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 :=
  mem_openAKLTGroundSpaceGeneralS_iff (by norm_num) hS Φ

/-- **General-`L` signature pin.** -/
example {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS L S
      ↔ ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 :=
  mem_openAKLTGroundSpaceGeneralS_iff hL hS Φ

end LatticeSystem.Tests.GeneralSOpenChainGroundSpace
