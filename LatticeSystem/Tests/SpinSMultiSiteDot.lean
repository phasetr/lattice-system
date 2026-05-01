import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Test coverage for the multi-site spin-`S` two-site dot product
(Tasaki §2.5 Phase B-β β-3c)
-/

namespace LatticeSystem.Tests.SpinSMultiSiteDot

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Symmetry of the two-site dot product. -/
example (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) = spinSDot y x N :=
  spinSDot_comm x y N

/-- Same-site Casimir: `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1`. -/
example (x : Λ) (N : ℕ) :
    (spinSDot x x N : ManyBodyOpS Λ N) =
      ((N : ℂ) * (N + 2) / 4) • 1 :=
  spinSDot_self x N

end LatticeSystem.Tests.SpinSMultiSiteDot
