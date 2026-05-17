import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Ladder/Cartan annihilation and 12sq actions on the Néel state

This companion file holds the cross-ladder annihilation theorems
(`Ŝ^± · Ŝ^± · |Φ_Néel⟩ = 0` patterns) and the transverse
`(Ŝ^(1))² + (Ŝ^(2))²` Casimir actions on the spin-`1/2` Néel state.
Extracted from `SublatticeCasimirNeel.lean` at refactor #54 (PR #3149)
to reduce the parent's transitive import cost (13.3s after the
PR #3129-#3148 sweep, post-refactor #53 drift back above the ~10s
threshold).

Contents:
- 7 cross-ladder annihilation theorems (S+/S- combinations vanish on Néel).
- `(Ŝ_A^(1))² + (Ŝ_A^(2))²` Casimir action on `|Φ_Néel⟩` (canonical sublattice).
- `Ŝ_A^+ · Ŝ_A^- · |Φ_Néel⟩ = |A| · |Φ_Néel⟩` (Cartan formula 2s = |A|).
- `(Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²` Casimir action on `|Φ_Néel⟩` (complement).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `Ŝ_A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 81:
the cross-ladder product annihilates the Néel state via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 83:
cross-ladder lowering annihilates Néel via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpMinus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 85:
cross-ladder raising annihilates Néel via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementPlus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 89: uses
cross-commute to swap factors, then `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [(sublatticeSpinHalfOpPlus_cross_commute A).eq]
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 91:
trivial via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpComplementPlus_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `((Ŝ_A^(1))² + (Ŝ_A^(2))²) · |Φ_Néel⟩ = (|A|/2) · |Φ_Néel⟩`. Spin-`1/2`
mirror of γ-4 step 95: derived as `(Ŝ_A)² · Néel - (Ŝ_A^(3))² · Néel`,
where `(Ŝ_A)²` has eigenvalue `|A|(|A|+2)/4` and `(Ŝ_A^(3))²` has
eigenvalue `(|A|/2)² = |A|²/4`. -/
theorem sublatticeSpinHalfOp12sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

/-- `Ŝ_A^+·Ŝ_A^- · |Φ_Néel⟩ = |A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 100: highest-weight Casimir formula 2s = |A| for s = |A|/2. -/
theorem sublatticeSpinHalfOpPlus_minus_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpPlus_mul_sublatticeSpinHalfOpMinus_eq]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOp12sq_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [← add_smul]
  congr 1
  ring

/-- `((Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²) · |Φ_Néel⟩ = (|¬A|/2) · |Φ_Néel⟩`.
Spin-`1/2` complement of γ-4 step 96. -/
theorem sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x) +
      sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_complement_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_complement_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x)).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

end LatticeSystem.Quantum
