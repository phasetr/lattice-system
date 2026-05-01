/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowExtend

/-!
# Test coverage for one-step matrix-power extension
-/

namespace LatticeSystem.Tests.MarshallLiebMattisMatrixPowExtend

open LatticeSystem.Math

example {B : Matrix (Fin 2) (Fin 2) ℝ} (hB_nn : ∀ i j, 0 ≤ B i j)
    {m : ℕ} {σ τ ρ : Fin 2}
    (hpow : 0 < (B ^ m) σ τ) (hstep : 0 < B τ ρ) :
    0 < (B ^ (m + 1)) σ ρ :=
  matrix_pow_succ_pos_of_pow_pos_step hB_nn hpow hstep

end LatticeSystem.Tests.MarshallLiebMattisMatrixPowExtend
