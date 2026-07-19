import LatticeSystem.Quantum.SpinS.MultiSite

/-!
# Spin-one site-component selector

This module provides the common axis selector for a spin-one operator at a
site of a finite ring. It is shared by the string-order construction in
Tasaki §7.2.1 and the large-`D` analysis in §8.1.1.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer, 2020, §7.2.1, eq. (7.2.6), p. 193, and §8.1.1,
eq. (8.1.3), p. 228.
-/

namespace LatticeSystem.Quantum

variable {L : ℕ}

/-- The site-`x` spin component `Ŝ_x^{(α)}` selected by `α : Fin 3`
(`0 ↦ Ŝ^{(1)}`, `1 ↦ Ŝ^{(2)}`, `2 ↦ Ŝ^{(3)}`) on a spin-one ring. -/
noncomputable def spinSSiteComponentS (α : Fin 3) (x : Fin L) : ManyBodyOpS (Fin L) 2 :=
  ![spinSSiteOp1 x 2, spinSSiteOp2 x 2, spinSSiteOp3 x 2] α

end LatticeSystem.Quantum
