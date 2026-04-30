/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.Connectivity

/-!
# Test coverage for swap-connectivity (Tasaki §2.5 Property (iii))
-/

namespace LatticeSystem.Tests.MarshallLiebMattisConnectivity

open LatticeSystem.Quantum

/-- Reflexivity. -/
example (G : SimpleGraph (Fin 2)) (σ : Fin 2 → Fin 2) :
    SwapReachable G σ σ :=
  SwapReachable.refl G σ

/-- Single-edge swap step. -/
example (G : SimpleGraph (Fin 2)) (hadj : G.Adj 0 1)
    (σ : Fin 2 → Fin 2) (h : σ 0 ≠ σ 1) :
    SwapReachable G σ (basisSwap σ 0 1) :=
  SwapReachable.of_step ⟨0, 1, hadj, h, rfl⟩

/-- Walk-induction for any walk x → y. -/
example (G : SimpleGraph (Fin 2)) {x y : Fin 2} (w : G.Walk x y)
    {σ : Fin 2 → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) :=
  swapReachable_of_walk_of_ne w h

/-- Reachability-based version. -/
example (G : SimpleGraph (Fin 2)) (hG : G.Preconnected)
    (x y : Fin 2) {σ : Fin 2 → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) :=
  swapReachable_of_preconnected_of_ne hG x y h

end LatticeSystem.Tests.MarshallLiebMattisConnectivity
