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

end LatticeSystem.Tests.SpinSMagnetization
