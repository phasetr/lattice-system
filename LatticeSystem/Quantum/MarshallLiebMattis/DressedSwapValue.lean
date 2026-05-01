/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapValue
import LatticeSystem.Quantum.MarshallLiebMattis.H0Matrix

/-!
# Dressed Heisenberg matrix entry value on swap-related configurations

This module assembles the **explicit value** of the dressed
Heisenberg matrix entry between configurations related by a single
bond swap on a bipartite graph, for **symmetric** real coupling `J`
supported on bipartite bonds:

  `dressedHeisenbergMatrixH0 A J σ τ = -(J x y).re`

where `τ.val = basisSwap σ.val x y` and the bond `(x, y)` crosses
the bipartition (`A x ≠ A y`) with antiparallel `σ_x ≠ σ_y`.

Combining:

* the Marshall sign trick (PR α-3:
  `marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel`)
  giving sign factor `-1`, and
* the Heisenberg matrix entry value (PR α-5h:
  `heisenbergHamiltonian_apply_basisSwap`) giving
  `(J x y + J y x) / 2 = J x y` for symmetric `J`,

the complex-valued dressed pairing equals `-J x y`. Taking the
real part (via PR α-2's `J` real hypothesis) gives `-(J x y).re`.

For `J(x, y).re > 0` (positive on graph edges), the negation gives
`-(J x y).re < 0`, hence the shifted matrix `B = c·I − M` has
`B σ τ > 0` strictly — the strict positivity needed for the
Perron–Frobenius irreducibility argument (subsequent PRs).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (proof of Theorem 2.2).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The dressed pairing on swap-related configurations.

For a bipartite graph `(Λ, A)`, real symmetric coupling `J`,
`x ≠ y` with `A x ≠ A y`, and antiparallel `σ_x ≠ σ_y`:

  `marshallSignOf A σ · marshallSignOf A (basisSwap σ x y) ·
   (heisenbergHamiltonian J) σ (basisSwap σ x y) = -(J x y)`. -/
theorem dressed_pairing_basisSwap_eq
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x)
    {x y : Λ} (hxy : x ≠ y) (hA : A x ≠ A y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    marshallSignOf A σ * marshallSignOf A (basisSwap σ x y) *
        (heisenbergHamiltonian J) σ (basisSwap σ x y) = -J x y := by
  rw [marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel A hxy hA h]
  rw [heisenbergHamiltonian_apply_basisSwap J hxy h]
  -- Symmetric J: J y x = J x y, so (J x y + J y x) / 2 = J x y.
  rw [show J y x = J x y from (hJ_symm x y).symm]
  rw [show (J x y + J x y) / 2 = J x y from by ring]
  ring

/-- The dressed Heisenberg matrix entry on swap-related H_0
configurations equals `-(J x y).re`. -/
theorem dressedHeisenbergMatrixH0_apply_basisSwap
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x)
    {x y : Λ} (hxy : x ≠ y) (hA : A x ≠ A y)
    {σ : H₀Index Λ} (h : σ.val x ≠ σ.val y)
    (τ : H₀Index Λ) (hτ : τ.val = basisSwap σ.val x y) :
    dressedHeisenbergMatrixH0 A J σ τ = -((J x y).re) := by
  unfold dressedHeisenbergMatrixH0
  rw [hτ, dressed_pairing_basisSwap_eq A hJ_symm hxy hA h, Complex.neg_re]

end LatticeSystem.Quantum
