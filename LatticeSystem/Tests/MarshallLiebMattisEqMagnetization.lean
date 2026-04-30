/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetization

/-!
# Test coverage for magnetisation preservation under `basisSwap`
-/

namespace LatticeSystem.Tests.MarshallLiebMattisEqMagnetization

open LatticeSystem.Quantum

/-- `basisSwap` preserves magnetization. -/
example (σ : Fin 2 → Fin 2) (x y : Fin 2) :
    magnetization (Fin 2) (basisSwap σ x y) = magnetization (Fin 2) σ :=
  magnetization_basisSwap σ x y

/-- `basisSwap` preserves the H_0 (zero magnetization) condition. -/
example (σ : Fin 2 → Fin 2) (x y : Fin 2) :
    magnetization (Fin 2) (basisSwap σ x y) = 0 ↔ magnetization (Fin 2) σ = 0 :=
  magnetization_basisSwap_eq_zero_iff σ x y

end LatticeSystem.Tests.MarshallLiebMattisEqMagnetization
