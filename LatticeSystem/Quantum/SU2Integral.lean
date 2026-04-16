/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.ManyBody
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# SU(2)-averaged state infrastructure (Tasaki §2.2 Problem 2.2.c)

Imports the interval-integral and trig-integral machinery from mathlib
that is needed to state and prove the SU(2)-averaged-state identity

```
(1/4π) ∫₀²π dφ ∫₀π dθ sin θ · (Û^(3)_φ · Û^(2)_θ · |ψ^↑⟩) ⊗ |ψ^↓⟩
= (1/2)(|↑↓⟩ - |↓↑⟩)
```

(Tasaki *Physics and Mathematics of Quantum Many-Body Systems*,
§2.2, Problem 2.2.c, eq. (2.2.15)).

This module currently provides only the **import bridge**: it brings
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` and
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic` into the project,
making `∫ x in a..b, f x` and standard trig integrals
(`integral_sin`, `integral_cos`, etc.) available.

The full integral statement and proof require component-wise expansion
of the rotated state (using `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp`
from `SpinHalfRotation.lean`), followed by standard trig-integral
evaluations. This is tracked as the next work item (B-3c, work 0020).
-/

namespace LatticeSystem.Quantum

-- This module serves as an import bridge. The integral statement
-- and proof will be added in B-3c (work 0020) once the component-wise
-- trig integrals are verified.

end LatticeSystem.Quantum
