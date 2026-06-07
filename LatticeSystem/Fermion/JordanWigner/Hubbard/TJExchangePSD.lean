import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondHalf
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki 11.5.3: the t-J exchange operator is positive-semidefinite (Theorem 11.26 PR3e)

The exchange (ferromagnetic Heisenberg) operator `tJExchange N G = Σ_{x,y} [G.Adj] (n̂_x n̂_y/4 −
Ŝ_x·Ŝ_y)` is a graph sum of per-bond singlet projectors, each positive-semidefinite
(`tJExchangeBond_posSemidef`); off-bond summands are `0`.  Hence:

* `tJExchange_posSemidef` — `(tJExchange N G).PosSemidef`.

This is the operator nonnegativity behind the half-filling ground energy `= 0` (the all-up state,
annihilated by `tJExchange`, sits at the bottom).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **The t-J exchange operator is positive-semidefinite.**  `tJExchange N G ≥ 0`: a graph sum of
per-bond positive-semidefinite Heisenberg terms (off-bond summands vanish). -/
theorem tJExchange_posSemidef (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] :
    (tJExchange N G).PosSemidef := by
  rw [tJExchange]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro x _
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro y _
  by_cases hadj : G.Adj x y
  · rw [if_pos hadj]
    exact tJExchangeBond_posSemidef x y hadj.ne
  · rw [if_neg hadj]
    exact Matrix.PosSemidef.zero

end LatticeSystem.Fermion
