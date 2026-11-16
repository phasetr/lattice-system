module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Finite-site spin operators

Coordinate spin components in the descending magnetic product basis.
-/

@[expose] public section

open scoped BigOperators

namespace LatticeSystem

/-- The three spin components at site `x` for positive doubled spin `n`.

Local indices have magnetic value `(n.val : ℝ) / 2 - (i.val : ℝ)`; axes `0`, `1`, `2` are
the first, second and third spin components. Configurations index the fixed
product basis of a finite system. The local matrices and their site action
follow Tasaki's equations (2.1.2), (2.1.3) and (2.2.4).
-/
noncomputable def spinAt {V : Type*} [Fintype V] [DecidableEq V]
    (n : {n : Nat // 0 < n}) (x : V) :
    Fin 3 → Matrix (V → Fin (n.val + 1)) (V → Fin (n.val + 1)) ℂ :=
  let spin : ℝ := (n.val : ℝ) / (1 + 1)
  let magnetic : Fin (n.val + 1) → ℝ := fun i => spin - (i.val : ℝ)
  let raising : Matrix (Fin (n.val + 1)) (Fin (n.val + 1)) ℂ :=
    fun row column => if row.val + 1 == column.val then
      (Real.sqrt (spin * (spin + 1) - magnetic column * (magnetic column + 1)) : ℂ)
    else 0
  let lowering := raising.conjTranspose
  let third : Matrix (Fin (n.val + 1)) (Fin (n.val + 1)) ℂ :=
    Matrix.diagonal fun i => ((magnetic i : ℝ) : ℂ)
  let components : Fin 3 → Matrix (Fin (n.val + 1)) (Fin (n.val + 1)) ℂ :=
    fun axis => if axis.val == 0 then (1 + 1 : ℂ)⁻¹ • (raising + lowering)
      else if axis.val == 1 then ((1 + 1) * Complex.I)⁻¹ • (raising - lowering)
      else third
  fun axis source target => components axis (source x) (target x) *
    ∏ site ∈ Finset.univ.erase x, if source site == target site then 1 else 0

end LatticeSystem
