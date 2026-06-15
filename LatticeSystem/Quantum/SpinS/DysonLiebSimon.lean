import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# Tasaki §4.1: the staggered order operator (toward Theorem 4.1, Dyson–Lieb–Simon)

For the antiferromagnetic Heisenberg model on the `d`-dimensional hypercubic lattice, Theorem 4.1
(Dyson–Lieb–Simon / Neves–Perez / Kennedy–Lieb–Shastry) asserts genuine **Néel long-range order**
when `d ≥ 3` (any spin `S`) or `d = 2` and `S ≥ 1`: the staggered order parameter is bounded below
*uniformly in the system size*, `⟨Φ_GS| (Ô_L^{(α)})² / L^d |Φ_GS⟩ ≥ q₀ > 0` (eq. (4.1.7)), where
`Ô_L^{(α)} = Σ_x ε_x Ŝ_x^{(α)}` is the staggered magnetization (`ε_x = ±1` the sublattice sign).

The order operator itself is a clean finite-volume object, which we define and characterize here:
`staggeredOrderOpS` together with its Hermiticity (`staggeredOrderOpS_isHermitian`), so that its
squared expectation `⟨Φ, (Ô)² Φ⟩` is a real, nonnegative order parameter.

The Néel-LRO statement (eq. (4.1.7)) is a deep theorem whose **faithful, sound** formalization
requires the actual `d`-dimensional hypercubic torus with nearest-neighbor antiferromagnetic
coupling — the uniform-in-`L` lower bound is *false* for arbitrary finite bipartite graphs (e.g.
with vanishing coupling) — and its proof rests on reflection positivity and infrared
(Gaussian-domination) bounds.  It is therefore deferred until the hypercubic-lattice /
reflection-positivity framework is in place.  (Infinite-volume systems are in scope — the
project's central long-term goal — so this is a deferral pending infrastructure, not an exclusion
from scope.)

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

/-- The staggered order operator is **Hermitian**: it is a real (`±1`) linear combination of the
Hermitian single-site spin-`3` operators `Ŝ_x^{(3)}`, so its squared expectation
`⟨Φ, (Ô)² Φ⟩` is real and nonnegative — a genuine order parameter. -/
theorem staggeredOrderOpS_isHermitian (A : Λ → Bool) (N : ℕ) :
    (staggeredOrderOpS (Λ := Λ) A N).IsHermitian := by
  refine Matrix.isHermitian_sum Finset.univ (fun x _ => ?_)
  refine Matrix.IsHermitian.smul ?_ ?_
  · rw [spinSSiteOp3_def]
    exact onSiteS_isHermitian x (spinSOp3_isHermitian N)
  · by_cases h : A x
    · simp [h, IsSelfAdjoint, star_one]
    · simp [h, IsSelfAdjoint]

end LatticeSystem.Quantum
