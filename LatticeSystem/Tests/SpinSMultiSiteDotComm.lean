import LatticeSystem.Quantum.SpinS.MultiSiteDotComm

/-!
# Test coverage for `[Ŝ_x · Ŝ_y, Ŝ_tot^(α)] = 0`
(Tasaki §2.5 Phase B-β β-3m)
-/

namespace LatticeSystem.Tests.SpinSMultiSiteDotComm

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Axis-3 SU(2) invariance: `[Ŝ_x · Ŝ_y, Ŝ_tot^(3)] = 0`. -/
example (x y : Λ) (N : ℕ) :
    spinSDot x y N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * spinSDot x y N = 0 :=
  spinSDot_commutator_totalSpinSOp3 x y N

/-- Axis-1 SU(2) invariance. -/
example (x y : Λ) (N : ℕ) :
    spinSDot x y N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * spinSDot x y N = 0 :=
  spinSDot_commutator_totalSpinSOp1 x y N

/-- Axis-2 SU(2) invariance. -/
example (x y : Λ) (N : ℕ) :
    spinSDot x y N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * spinSDot x y N = 0 :=
  spinSDot_commutator_totalSpinSOp2 x y N

end LatticeSystem.Tests.SpinSMultiSiteDotComm
