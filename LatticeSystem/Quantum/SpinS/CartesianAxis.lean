import LatticeSystem.Quantum.SpinS.AndersonTower
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Cartesian axis foundation for spin-`S` order and total-spin operators

Lightweight foundation layer holding the `Fin 3` axis-indexing conventions shared by the
Anderson-tower arguments: the Levi-Civita scalar `leviCivita3`, the axis-indexed staggered order
operator vector `stagOpVec`, and the total-spin generator vector `totalSpinSOpVec`.  Keeping these
three definitions below the proof modules lets consumers depend on the axis conventions without
depending on the sphere-average or rotation-commutator proof layers.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.58)–(4.2.59), p.108; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **Levi-Civita symbol** `ε_{γβδ}` on `Fin 3`, valued in `ℂ`: the totally antisymmetric scalar
normalised by `ε_{012} = 1`, taking the value `+1` on the even permutations `(0,1,2)`, `(1,2,0)`,
`(2,0,1)`, the value `−1` on the odd permutations `(0,2,1)`, `(1,0,2)`, `(2,1,0)`, and `0` whenever
two indices coincide.  Carrying the axis double index of the swap-band contraction as this `ℂ`
scalar lets the `Finset.sum` over axes absorb the case analysis. -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℂ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 1, 0, 2 => -1
  | 2, 1, 0 => -1
  | _, _, _ => 0

/-- The **axis-indexed staggered order operator vector** `α ↦ ô^{(α)}`: axis `0` is
`staggeredOrderOp1S`, axis `1` is `staggeredOrderOp2S`, axis `2` is the `3`-axis operator
`staggeredOrderOpS`.  It packages the three components so that `directionStaggeredOp` is the
`n`-weighted sum `Σ_α n_α ô^{(α)}` (`directionStaggeredOp_eq_sum`). -/
noncomputable def stagOpVec (A : Λ → Bool) (N : ℕ) : Fin 3 → ManyBodyOpS Λ N :=
  ![staggeredOrderOp1S A N, staggeredOrderOp2S A N, staggeredOrderOpS A N]

/-- The **total-spin generator vector** `γ ↦ Ŝ^{(γ)}_tot`: axis `0` is `totalSpinSOp1`, axis `1` is
`totalSpinSOp2`, axis `2` is `totalSpinSOp3`.  It bundles the three Cartesian total-spin generators
over the axis index `Fin 3`, mirroring the staggered order vector `stagOpVec`, so that the rotation
commutator `[Ŝ^{(γ)}_tot, ô^{(β)}]` can be stated uniformly in the axis indices. -/
noncomputable def totalSpinSOpVec (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    Fin 3 → ManyBodyOpS Λ N :=
  ![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N]

end LatticeSystem.Quantum
