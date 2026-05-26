import LatticeSystem.Quantum.SpinHalf

/-!
# Basis states and raising/lowering operators for S = 1/2

Formalizes Tasaki *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eqs. (2.1.4), (2.1.5), (2.1.6), pp. 14.

* Computational-basis column vectors `|ψ^↑⟩ = (1, 0)ᵀ` and
  `|ψ^↓⟩ = (0, 1)ᵀ` (eq. (2.1.6) for `S = 1/2`, `σ = ±1/2`).
* Eigenvalue equation (eq. (2.1.4)):
  `Ŝ^(3) |ψ^↑⟩ = (1/2) |ψ^↑⟩`, `Ŝ^(3) |ψ^↓⟩ = -(1/2) |ψ^↓⟩`.
* Raising and lowering operators `Ŝ^± := Ŝ^(1) ± i · Ŝ^(2)`, proved to
  equal the strictly triangular unit matrices `!![0,1;0,0]` and
  `!![0,0;1,0]`.
* Action (eq. (2.1.5)):
  `Ŝ^+ |ψ^↑⟩ = 0`, `Ŝ^- |ψ^↑⟩ = |ψ^↓⟩`,
  `Ŝ^+ |ψ^↓⟩ = |ψ^↑⟩`, `Ŝ^- |ψ^↓⟩ = 0`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Basis states (Tasaki eq 2.1.6, p. 14) -/

/-- The computational-basis up state `|ψ^↑⟩ = (1, 0)ᵀ`. -/
def spinHalfUp : Fin 2 → ℂ := ![1, 0]

/-- The computational-basis down state `|ψ^↓⟩ = (0, 1)ᵀ`. -/
def spinHalfDown : Fin 2 → ℂ := ![0, 1]

/-! ## Eigenvalue equation (Tasaki eq 2.1.4, p. 14) -/

/-- `Ŝ^(3) |ψ^↑⟩ = (1/2) |ψ^↑⟩`. -/
theorem spinHalfOp3_mulVec_spinHalfUp :
    spinHalfOp3.mulVec spinHalfUp = (1 / 2 : ℂ) • spinHalfUp := by
  ext i
  fin_cases i <;>
    simp [spinHalfOp3, spinHalfUp, pauliZ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply]

/-- `Ŝ^(3) |ψ^↓⟩ = -(1/2) |ψ^↓⟩`. -/
theorem spinHalfOp3_mulVec_spinHalfDown :
    spinHalfOp3.mulVec spinHalfDown = -(1 / 2 : ℂ) • spinHalfDown := by
  ext i
  fin_cases i <;>
    simp [spinHalfOp3, spinHalfDown, pauliZ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply]

/-! ## Raising and lowering operators (Tasaki p. 14) -/

/-- Raising operator: `Ŝ^+ = (0, 1; 0, 0)` in the computational basis. -/
def spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- Lowering operator: `Ŝ^- = (0, 0; 1, 0)` in the computational basis. -/
def spinHalfOpMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 1, 0]

/-- The defining identity `Ŝ^+ = Ŝ^(1) + i · Ŝ^(2)`. -/
theorem spinHalfOpPlus_eq_add :
    spinHalfOpPlus = spinHalfOp1 + I • spinHalfOp2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOp1, spinHalfOp2, pauliX, pauliY] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> ring

/-- The defining identity `Ŝ^- = Ŝ^(1) - i · Ŝ^(2)`. -/
theorem spinHalfOpMinus_eq_sub :
    spinHalfOpMinus = spinHalfOp1 - I • spinHalfOp2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpMinus, spinHalfOp1, spinHalfOp2, pauliX, pauliY] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> ring

/-- `σ^+ · σ^z = -σ^+`: the raising operator anticommutes with `σ^z`
(right multiplication flips the sign, since `σ^+` maps the down state
`|↓⟩` to `|↑⟩`, and `|↓⟩` has `σ^z`-eigenvalue `-1`). -/
theorem spinHalfOpPlus_mul_pauliZ :
    spinHalfOpPlus * pauliZ = -spinHalfOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^z · σ^+ = σ^+`: the raising operator commutes with `σ^z`
on the left (left multiplication preserves the sign, since `σ^+ |↓⟩
= |↑⟩` has `σ^z`-eigenvalue `+1`). -/
theorem pauliZ_mul_spinHalfOpPlus :
    pauliZ * spinHalfOpPlus = spinHalfOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^+ · σ^+ = 0`: the raising operator squares to zero (Pauli
exclusion: cannot raise twice). -/
theorem spinHalfOpPlus_mul_self :
    spinHalfOpPlus * spinHalfOpPlus = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^+ · σ^- · σ^+ = σ^+`: the projector `σ^+ σ^- = |↑⟩⟨↑|`
applied to `σ^+` returns `σ^+` (since `σ^+` lands in the up-state
range). -/
theorem spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus :
    spinHalfOpPlus * spinHalfOpMinus * spinHalfOpPlus = spinHalfOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOpMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The fermion number matrix `σ^- · σ^+ = !![0,0;0,1]` commutes with
`σ^z = !![1,0;0,-1]` as matrices (both diagonal in the computational
basis). -/
theorem spinHalfOpMinus_mul_spinHalfOpPlus_commute_pauliZ :
    Commute (spinHalfOpMinus * spinHalfOpPlus) pauliZ := by
  change spinHalfOpMinus * spinHalfOpPlus * pauliZ =
    pauliZ * (spinHalfOpMinus * spinHalfOpPlus)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOpMinus, pauliZ, Matrix.mul_apply,
      Fin.sum_univ_two]

/-! ## Raising/lowering actions (Tasaki eq 2.1.5, p. 14) -/

/-- `Ŝ^+ |ψ^↑⟩ = 0`. -/
theorem spinHalfOpPlus_mulVec_spinHalfUp :
    spinHalfOpPlus.mulVec spinHalfUp = 0 := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpPlus, spinHalfUp, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- `Ŝ^- |ψ^↑⟩ = |ψ^↓⟩`. -/
theorem spinHalfOpMinus_mulVec_spinHalfUp :
    spinHalfOpMinus.mulVec spinHalfUp = spinHalfDown := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpMinus, spinHalfUp, spinHalfDown, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- `Ŝ^+ |ψ^↓⟩ = |ψ^↑⟩`. -/
theorem spinHalfOpPlus_mulVec_spinHalfDown :
    spinHalfOpPlus.mulVec spinHalfDown = spinHalfUp := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpPlus, spinHalfUp, spinHalfDown, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- `Ŝ^- |ψ^↓⟩ = 0`. -/
theorem spinHalfOpMinus_mulVec_spinHalfDown :
    spinHalfOpMinus.mulVec spinHalfDown = 0 := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpMinus, spinHalfDown, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-! ## Adjoint relations between raising and lowering -/

/-- `(Ŝ^+)† = Ŝ^-`. -/
theorem spinHalfOpPlus_conjTranspose :
    (spinHalfOpPlus)ᴴ = spinHalfOpMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOpMinus, Matrix.conjTranspose_apply]

/-- `(Ŝ^-)† = Ŝ^+`. -/
theorem spinHalfOpMinus_conjTranspose :
    (spinHalfOpMinus)ᴴ = spinHalfOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOpMinus, Matrix.conjTranspose_apply]

/-! ## Single-site ladder commutator `[Ŝ^+, Ŝ^-] = 2 · Ŝ^(3)` -/

/-- The ladder commutator: `[Ŝ^+, Ŝ^-] = 2 · Ŝ^(3)`. -/
theorem spinHalfOpPlus_commutator_spinHalfOpMinus :
    spinHalfOpPlus * spinHalfOpMinus - spinHalfOpMinus * spinHalfOpPlus =
      (2 : ℂ) • spinHalfOp3 := by
  unfold spinHalfOpPlus spinHalfOpMinus spinHalfOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.sub_apply, pauliZ]

end LatticeSystem.Quantum
