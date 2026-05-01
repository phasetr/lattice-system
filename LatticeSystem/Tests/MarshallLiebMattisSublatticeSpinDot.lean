/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot

/-!
# Test coverage for the cross-sublattice spin dot product
-/

namespace LatticeSystem.Tests.MarshallLiebMattisSublatticeSpinDot

open LatticeSystem.Quantum

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^(α) Ŝ_B^(α)`. -/
example (A B : Fin 2 → Bool) :
    sublatticeSpinDot A B =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 B :=
  sublatticeSpinDot_def A B

/-- `Ŝ_A · Ŝ_B` expands as `Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`. -/
example (A B : Fin 2 → Bool) :
    sublatticeSpinDot A B =
      ∑ x : Fin 2, ∑ y : Fin 2,
        if A x ∧ B y then spinHalfDot x y else 0 :=
  sublatticeSpinDot_eq_sum_sum A B

/-- `Ŝ_A · Ŝ_¬A` is Hermitian. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinDot A (fun x => ! A x)).IsHermitian :=
  sublatticeSpinDot_complement_isHermitian A

/-- `(Ŝ_A)² = Σ_{x ∈ A} Σ_{y ∈ A} Ŝ_x · Ŝ_y`. -/
example (A : Fin 2 → Bool) :
    sublatticeSpinHalfSquared A =
      ∑ x : Fin 2, ∑ y : Fin 2,
        if A x ∧ A y then spinHalfDot x y else 0 :=
  sublatticeSpinHalfSquared_eq_sum_dot A

/-- `(Ŝ_A)² · |↑↑⟩ = (|A|·(|A|+2)/4) · |↑↑⟩`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (basisVec (fun _ : Fin 2 => (0 : Fin 2))) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Fin 2 => A x = true)).card + 2) / 4) •
        basisVec (fun _ : Fin 2 => (0 : Fin 2)) :=
  sublatticeSpinHalfSquared_mulVec_basisVec_all_up A

end LatticeSystem.Tests.MarshallLiebMattisSublatticeSpinDot
