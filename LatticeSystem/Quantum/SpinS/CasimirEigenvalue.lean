/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Casimir

/-!
# Spin-`S` Casimir eigenvalue on basis vectors (Tasaki §2.1 P1d''' β-17)

The Casimir identity `(Ŝ)² = (N(N+2)/4) · 1` (β-14) immediately
implies that every basis vector `|k⟩` is a `(Ŝ)²` eigenvector with
the universal eigenvalue:

  `(Ŝ^{(1)})² · |k⟩ + (Ŝ^{(2)})² · |k⟩ + (Ŝ^{(3)})² · |k⟩ = (N(N+2)/4) · |k⟩`.

This is the standard quantum-mechanical statement that every state
of the spin-`S` representation has Casimir value `S(S+1) = (N/2)(N/2+1)`,
reflecting that the representation is a single irreducible (Schur).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `(Ŝ)² · |k⟩ = (N(N+2)/4) · |k⟩`: every basis vector is a Casimir
eigenvector with the universal eigenvalue. -/
theorem spinSOp_total_squared_mulVec_basis (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N +
        spinSOp3 N * spinSOp3 N).mulVec (Pi.single k 1) =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • (Pi.single k 1 : Fin (N + 1) → ℂ) := by
  rw [spinSOp_total_squared]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

end LatticeSystem.Quantum
