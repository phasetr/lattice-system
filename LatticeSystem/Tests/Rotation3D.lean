/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.Rotation3D

/-!
# Test coverage for Quantum/Rotation3D

A+B+D coverage for `rot3D{1,2,3}Pi` (per refactor plan v4 §9 mapping
table; refactor Phase 1 PR 13, #281).
-/

namespace LatticeSystem.Tests.Rotation3D

open LatticeSystem.Quantum

/-! ## D. `(R^(α)_π)² = 1` for the 3D π-rotations -/

example : rot3D1Pi * rot3D1Pi = 1 := rot3D1Pi_sq
example : rot3D2Pi * rot3D2Pi = 1 := rot3D2Pi_sq
example : rot3D3Pi * rot3D3Pi = 1 := rot3D3Pi_sq

end LatticeSystem.Tests.Rotation3D
