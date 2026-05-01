/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin

/-!
# Test coverage for the sublattice spin operators
-/

namespace LatticeSystem.Tests.MarshallLiebMattisSublatticeSpin

open LatticeSystem.Quantum

/-- `Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_¬A^(α)` for axes 1, 2, 3. -/
example (A : Fin 2 → Bool) :
    totalSpinHalfOp1 (Fin 2) =
      sublatticeSpinHalfOp1 A + sublatticeSpinHalfOp1 (fun x => ! A x) :=
  totalSpinHalfOp1_eq_sublattice_sum A

/-- `Ŝ_A^(α)` is Hermitian (axis 1). -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinHalfOp1 A).IsHermitian :=
  sublatticeSpinHalfOp1_isHermitian A

/-- `Ŝ_A^(α) Ŝ_¬A^(α)` commutes (axis 1). -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfOp1 A) (sublatticeSpinHalfOp1 (fun x => ! A x)) :=
  sublatticeSpinHalfOp1_cross_commute A

/-- `(Ŝ_A)²` is Hermitian. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinHalfSquared A).IsHermitian :=
  sublatticeSpinHalfSquared_isHermitian A

/-- Mixed-axes cross-commute: `Ŝ_A^(1)` and `Ŝ_¬A^(2)` commute. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfOp1 A) (sublatticeSpinHalfOp2 (fun x => ! A x)) :=
  sublatticeSpinHalfOp1_cross_commute_op2 A

/-- Mixed-axes cross-commute: `Ŝ_A^(2)` and `Ŝ_¬A^(3)` commute. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfOp2 A) (sublatticeSpinHalfOp3 (fun x => ! A x)) :=
  sublatticeSpinHalfOp2_cross_commute_op3 A

/-- Mixed-axes cross-commute: `Ŝ_A^(3)` and `Ŝ_¬A^(1)` commute. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfOp3 A) (sublatticeSpinHalfOp1 (fun x => ! A x)) :=
  sublatticeSpinHalfOp3_cross_commute_op1 A

end LatticeSystem.Tests.MarshallLiebMattisSublatticeSpin
