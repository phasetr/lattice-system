import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Test coverage for spin-`S` magnetization
(Tasaki §2.5 Phase B-β β-4a)
-/

namespace LatticeSystem.Tests.SpinSMagnetization

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `magSumS σ ≤ |Λ| · N`. -/
example {N : ℕ} (σ : Λ → Fin (N + 1)) :
    magSumS σ ≤ Fintype.card Λ * N :=
  magSumS_le σ

/-- Membership in `magSubspaceS` unfolds to the eigenvalue equation. -/
example {N : ℕ} (M : ℂ) (v : (Λ → Fin (N + 1)) → ℂ) :
    v ∈ magSubspaceS Λ N M ↔ (totalSpinSOp3 Λ N).mulVec v = M • v :=
  mem_magSubspaceS_iff M v

/-- Distinct sectors are disjoint. -/
example {N : ℕ} {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magSubspaceS Λ N M) (magSubspaceS Λ N M') :=
  magSubspaceS_disjoint hMM'

end LatticeSystem.Tests.SpinSMagnetization
