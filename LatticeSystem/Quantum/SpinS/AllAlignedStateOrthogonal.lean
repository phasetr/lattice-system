import LatticeSystem.Quantum.SpinS.AllAlignedStateDistinct
import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal

/-!
# All-aligned states at distinct constants are orthogonal

For `[Nonempty V]` and `c₁ ≠ c₂`,

  `dotProduct (star (allAlignedStateS V N c₁)) (allAlignedStateS V N c₂) = 0`.

Direct application of `basisVecS_inner_of_ne` (PR #914) combined
with `allAlignedConfigS_injective` (PR #956).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- All-aligned states at distinct constants are orthogonal. -/
theorem allAlignedStateS_inner_of_ne [Nonempty V] {c₁ c₂ : Fin (N + 1)}
    (hne : c₁ ≠ c₂) :
    dotProduct (star (allAlignedStateS V N c₁))
      (allAlignedStateS V N c₂) = 0 := by
  unfold allAlignedStateS
  apply basisVecS_inner_of_ne
  intro h
  exact hne (allAlignedConfigS_injective h.symm)

end LatticeSystem.Quantum
