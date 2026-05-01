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

/-- The two sublattice Casimirs commute: `Commute (Ŝ_A)² (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfSquared A)
            (sublatticeSpinHalfSquared (fun x => ! A x)) :=
  sublatticeSpinHalfSquared_cross_commute A

/-- Sublattice SU(2) algebra: `[Ŝ_A^(1), Ŝ_A^(2)] = i · Ŝ_A^(3)`. -/
example (A : Fin 2 → Bool) :
    sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp2 A
        - sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp1 A =
      Complex.I • sublatticeSpinHalfOp3 A :=
  sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 A

/-- Sublattice SU(2) algebra: `[Ŝ_A^(2), Ŝ_A^(3)] = i · Ŝ_A^(1)`. -/
example (A : Fin 2 → Bool) :
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A
        - sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A =
      Complex.I • sublatticeSpinHalfOp1 A :=
  sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 A

/-- Sublattice SU(2) algebra: `[Ŝ_A^(3), Ŝ_A^(1)] = i · Ŝ_A^(2)`. -/
example (A : Fin 2 → Bool) :
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A
        - sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A =
      Complex.I • sublatticeSpinHalfOp2 A :=
  sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^(1))`. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp1 A) :=
  sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp1 A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^(2))`. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp2 A) :=
  sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp2 A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^(3))`. -/
example (A : Fin 2 → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp3 A) :=
  sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp3 A

end LatticeSystem.Tests.MarshallLiebMattisSublatticeSpin
