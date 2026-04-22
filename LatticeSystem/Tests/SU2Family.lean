/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.SU2Integral

/-!
# Test coverage for the SU2 cluster

D coverage for `Quantum/SU2.lean` and `Quantum/SU2Integral.lean`
(per refactor plan v4 §9 mapping table; refactor Phase 1 PR 12,
#281).
-/

namespace LatticeSystem.Tests.SU2Family

open LatticeSystem.Quantum

/-! ## D. signature shims for `SU2` membership -/

/-- `Û^(1)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot1 θ ∈ SU2 := spinHalfRot1_mem_SU2 θ

/-- `Û^(2)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot2 θ ∈ SU2 := spinHalfRot2_mem_SU2 θ

/-- `Û^(3)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot3 θ ∈ SU2 := spinHalfRot3_mem_SU2 θ

/-- Euler product is in `SU(2)`. -/
example (φ θ ψ : ℝ) : spinHalfEulerProduct φ θ ψ ∈ SU2 :=
  spinHalfEulerProduct_mem_SU2 φ θ ψ

/-! ## D. signature shims for `SU2Integral` -/

example : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ = 0 :=
  integral_cos_zero_two_pi

example : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin θ = 0 :=
  integral_sin_zero_two_pi

example : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 :=
  integral_sin_zero_pi

end LatticeSystem.Tests.SU2Family
