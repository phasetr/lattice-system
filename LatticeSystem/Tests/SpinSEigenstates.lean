import LatticeSystem.Quantum.SpinS.Eigenstates

/-!
# Test coverage for spin-`S` eigenstates (Tasaki §2.1 P1d''' β-15)
-/

namespace LatticeSystem.Tests.SpinSEigenstates

open LatticeSystem.Quantum

/-- `Ŝ^{(3)} · |k⟩ = (N/2 − k) · |k⟩`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp3 N).mulVec (Pi.single k 1) =
      (((N : ℂ) / 2 - (k.val : ℂ))) • (Pi.single k 1 : Fin (N + 1) → ℂ) :=
  spinSOp3_mulVec_basis N k

end LatticeSystem.Tests.SpinSEigenstates
