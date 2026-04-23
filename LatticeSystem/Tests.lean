/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Tests.Foundation
import LatticeSystem.Tests.TestHelpers
import LatticeSystem.Tests.SpinDot
import LatticeSystem.Tests.TotalSpin
import LatticeSystem.Tests.SpinHalfRotation
import LatticeSystem.Tests.GibbsState
import LatticeSystem.Tests.MagnetizationSubspace
import LatticeSystem.Tests.SpinHalfFamily
import LatticeSystem.Tests.SpinOneFamily
import LatticeSystem.Tests.SU2Family
import LatticeSystem.Tests.Pauli
import LatticeSystem.Tests.Z2Z2
import LatticeSystem.Tests.Rotation3D
import LatticeSystem.Tests.Sanity
import LatticeSystem.Tests.Graph
import LatticeSystem.Tests.Heisenberg
import LatticeSystem.Tests.ManyBody
import LatticeSystem.Tests.Hubbard
import LatticeSystem.Tests.JordanWigner
import LatticeSystem.Tests.Ising
import LatticeSystem.Tests.JWAbstract
import LatticeSystem.Tests.Scale
import LatticeSystem.Tests.NeelState
import LatticeSystem.Tests.TimeReversalSpinHalf
import LatticeSystem.Tests.TimeReversalMulti

/-!
# Test aggregator for the `lattice-system` library

Imports every regression-test module under
`LatticeSystem.Tests.*`. Loaded via the `lakefile.toml`'s
default-targets list so `lake build` exercises the full test
surface alongside the source library `LatticeSystem`.

Test methods (A-G) and the per-module Tests/source mapping
follow `docs/refactoring-conventions.md` §1
([project page](https://phasetr.github.io/lattice-system/refactoring-conventions/#1-test-methods-per-refactor-plan-v4-§21)).
-/
