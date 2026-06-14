import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Tasaki §4.1: existence of Néel order (Theorem 4.1, Dyson–Lieb–Simon)

For the antiferromagnetic Heisenberg model on the `d`-dimensional hypercubic lattice, the ground
state has genuine **Néel long-range order** when `d ≥ 3` (any spin `S`) or `d = 2` and `S ≥ 1`: the
staggered order parameter is bounded below uniformly in the system size,
`⟨Φ_GS| (Ô_L^{(α)})² / L^d |Φ_GS⟩ ≥ q₀ > 0` (eq. (4.1.7)), where
`Ô_L^{(α)} = Σ_x ε_x Ŝ_x^{(α)}` is the staggered magnetization (`ε_x = ±1` the sublattice sign).

This is the celebrated Dyson–Lieb–Simon / Neves–Perez / Kennedy–Lieb–Shastry theorem, proved by
*reflection positivity* and infrared (Gaussian-domination) bounds.  The proof is a deep
infinite-volume argument; its essential content is the **uniformity in `L`** of the lower bound.  We
record it as a documented axiom (to be discharged once the reflection-positivity /
thermodynamic-limit framework is in place — infinite-volume systems are in scope, the project's
central long-term goal).

This file defines the **staggered order operator** `staggeredOrderOpS` and states Theorem 4.1.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.1, eq. (4.1.7), pp. 88–90; Dyson–Lieb–Simon (1978), Neves–Perez (1986),
Kennedy–Lieb–Shastry (1988).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The staggered (Néel) order operator** `Ô^{(3)} = Σ_x ε_x Ŝ_x^{(3)}` for a sublattice
assignment `A : Λ → Bool` (`ε_x = +1` on the `A`-sublattice, `−1` on the other).  Its expectation
measures Néel long-range order; by `SU(2)` invariance of the ground state the choice of spin
component (here `α = 3`) is immaterial. -/
noncomputable def staggeredOrderOpS (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOp3 x N

/-- **Tasaki Theorem 4.1 (Dyson–Lieb–Simon existence of Néel order), AXIOM.**  Fix a spin
`S = N/2` and a lattice dimension `d` with `d ≥ 3`, or `d = 2` and `S ≥ 1` (`1 ≤ N`).  Then there is
a positive constant `q₀` such that, for every sufficiently large `d`-dimensional hypercubic lattice
(here an abstract finite bipartite `Λ` of `L^d` sites with antiferromagnetic Heisenberg coupling `J`
— `J x y ≥ 0` across the bipartition), any ground state `Φ` of `heisenbergHamiltonianS J N`
(a minimum-energy eigenvector) has staggered order parameter bounded below *uniformly in the size*:
`q₀ ≤ ⟨Φ, (Ô^{(3)})² Φ⟩.re / |Λ|` (eq. (4.1.7)).

The uniformity in the system size is the content of the theorem (a single finite volume gives no
information).  Recorded as a documented axiom; the reflection-positivity / infrared-bound proof is
deferred (a deep infinite-volume argument). -/
axiom dyson_lieb_simon_neel_lro (d N : ℕ) (hdS : 3 ≤ d ∨ (d = 2 ∧ 1 ≤ N)) :
    ∃ q₀ : ℝ, 0 < q₀ ∧
      ∀ (L₀ : ℕ), ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool)
        (J : Λ → Λ → ℂ) (Φ : (Λ → Fin (N + 1)) → ℂ),
        L₀ ≤ Fintype.card Λ →
        (∀ x y, A x = A y → J x y = 0) →
        (∀ x y, 0 ≤ (J x y).re) →
        (∃ E₀ : ℂ, (heisenbergHamiltonianS J N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Λ → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (heisenbergHamiltonianS J N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧ Φ ≠ 0) →
        q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ)).re
          / (Fintype.card Λ : ℝ)

end LatticeSystem.Quantum
