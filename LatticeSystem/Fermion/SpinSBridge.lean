import LatticeSystem.Fermion.Mode
import LatticeSystem.Quantum.SpinS.SpinHalfSpecialization

/-!
# Single-mode fermion ↔ generic spin-`S` at `N = 1` bridge

Combines the existing `fermionAnnihilation_eq_spinHalfOpPlus` /
`fermionCreation_eq_spinHalfOpMinus` (`Fermion/Mode.lean`) with the
`spinSOpPlus_one_eq_spinHalfOpPlus` /
`spinSOpMinus_one_eq_spinHalfOpMinus` from PR #922
(`Quantum/SpinS/SpinHalfSpecialization.lean`) to provide a direct
identification at the spin-`S` level:

  `fermionAnnihilation = spinSOpPlus 1`
  `fermionCreation = spinSOpMinus 1`.

This transitive bridge enables transferring spin-`S` results
directly to single-mode fermion operators.

Tracked as part of Tasaki §2.1 / §2.4 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `fermionAnnihilation = spinSOpPlus 1`: bridges single-mode
fermion annihilation to generic spin-`S` raising operator at
`N = 1` (transitively via spin-`1/2` raising). -/
theorem fermionAnnihilation_eq_spinSOpPlus_one :
    fermionAnnihilation = LatticeSystem.Quantum.spinSOpPlus 1 := by
  rw [fermionAnnihilation_eq_spinHalfOpPlus,
    ← LatticeSystem.Quantum.spinSOpPlus_one_eq_spinHalfOpPlus]

/-- `fermionCreation = spinSOpMinus 1`: bridges single-mode fermion
creation to generic spin-`S` lowering operator at `N = 1`. -/
theorem fermionCreation_eq_spinSOpMinus_one :
    fermionCreation = LatticeSystem.Quantum.spinSOpMinus 1 := by
  rw [fermionCreation_eq_spinHalfOpMinus,
    ← LatticeSystem.Quantum.spinSOpMinus_one_eq_spinHalfOpMinus]

end LatticeSystem.Fermion
