import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDefCore

/-!
# Sublattice ladder operators and Cartan relations
(build-speed companion)

Build-speed companion to `SublatticeSpin.lean`. Hosts the trailing
sections "Sublattice ladder operators (raising / lowering on `A`)",
"Sublattice Cartan relations", edge cases (empty / full sublattice),
reverse identities, and the sublattice-axis-squared = conjTranspose
products (originally lines 642..998 of the pre-#38 parent file).

This is **separate** from the existing companion
`SublatticeSpinLadder.lean` (from refactor #28), which holds
ladder *applications* (realness / annihilation / adjoint /
magnetization-shift / Cartan identities / cross-sublattice
commute). The present companion holds the ladder *definitions*
and Cartan relations between sublattice generators.

Splitting these blocks out drops the parent from ~1000 lines to
~641 lines.

`SublatticeCasimirNeel.lean` updated to additionally import this
companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Edge cases: empty sublattice -/

/-- For the empty sublattice (`A = const false`), `Ŝ_A^(α)` vanishes. -/
theorem sublatticeSpinSOp1_const_false :
    sublatticeSpinSOp1 (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSOp1
  apply Finset.sum_eq_zero
  intro x _
  simp

/-- `Ŝ_A^(2)` vanishes on empty `A`. -/
theorem sublatticeSpinSOp2_const_false :
    sublatticeSpinSOp2 (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSOp2
  apply Finset.sum_eq_zero
  intro x _
  simp

/-- `Ŝ_A^(3)` vanishes on empty `A`. -/
theorem sublatticeSpinSOp3_const_false :
    sublatticeSpinSOp3 (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSOp3
  apply Finset.sum_eq_zero
  intro x _
  simp

/-- `(Ŝ_A)²` vanishes on empty `A`. -/
theorem sublatticeSpinSquaredS_const_false :
    sublatticeSpinSquaredS (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSquaredS
  rw [sublatticeSpinSOp1_const_false, sublatticeSpinSOp2_const_false,
      sublatticeSpinSOp3_const_false]
  simp

/-- `Ŝ_A^+` vanishes on empty `A`. -/
theorem sublatticeSpinSOpPlus_const_false :
    sublatticeSpinSOpPlus (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSOpPlus
  apply Finset.sum_eq_zero
  intro x _
  simp

/-- `Ŝ_A^-` vanishes on empty `A`. -/
theorem sublatticeSpinSOpMinus_const_false :
    sublatticeSpinSOpMinus (Λ := Λ) N (fun _ => false) = 0 := by
  unfold sublatticeSpinSOpMinus
  apply Finset.sum_eq_zero
  intro x _
  simp

/-! ## Edge cases: full sublattice -/

/-- For the full sublattice (`A = const true`), `Ŝ_A^(1)` equals the
total `Ŝ_tot^(1)`. -/
theorem sublatticeSpinSOp1_const_true :
    sublatticeSpinSOp1 (Λ := Λ) N (fun _ => true) = totalSpinSOp1 Λ N := by
  unfold sublatticeSpinSOp1 totalSpinSOp1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinSOp2_const_true :
    sublatticeSpinSOp2 (Λ := Λ) N (fun _ => true) = totalSpinSOp2 Λ N := by
  unfold sublatticeSpinSOp2 totalSpinSOp2
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinSOp3_const_true :
    sublatticeSpinSOp3 (Λ := Λ) N (fun _ => true) = totalSpinSOp3 Λ N := by
  unfold sublatticeSpinSOp3 totalSpinSOp3
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinSquaredS_const_true :
    sublatticeSpinSquaredS (Λ := Λ) N (fun _ => true) = totalSpinSSquared Λ N := by
  unfold sublatticeSpinSquaredS totalSpinSSquared
  rw [sublatticeSpinSOp1_const_true, sublatticeSpinSOp2_const_true,
      sublatticeSpinSOp3_const_true]

theorem sublatticeSpinSOpPlus_const_true :
    sublatticeSpinSOpPlus (Λ := Λ) N (fun _ => true) = totalSpinSOpPlus Λ N := by
  unfold sublatticeSpinSOpPlus totalSpinSOpPlus
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinSOpMinus_const_true :
    sublatticeSpinSOpMinus (Λ := Λ) N (fun _ => true) = totalSpinSOpMinus Λ N := by
  unfold sublatticeSpinSOpMinus totalSpinSOpMinus
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-! ## Reverse identities -/

/-- `Ŝ_A^+ + Ŝ_A^- = 2 • Ŝ_A^(1)`. Direct from `_eq_add` and `_eq_sub`. -/
theorem sublatticeSpinSOpPlus_add_sublatticeSpinSOpMinus (A : Λ → Bool) :
    sublatticeSpinSOpPlus N A + sublatticeSpinSOpMinus N A =
      (2 : ℂ) • sublatticeSpinSOp1 N A := by
  rw [sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub, two_smul]
  abel

/-- `Ŝ_A^+ - Ŝ_A^- = 2i • Ŝ_A^(2)`. Direct from `_eq_add` and `_eq_sub`. -/
theorem sublatticeSpinSOpPlus_sub_sublatticeSpinSOpMinus (A : Λ → Bool) :
    sublatticeSpinSOpPlus N A - sublatticeSpinSOpMinus N A =
      (2 * Complex.I) • sublatticeSpinSOp2 N A := by
  rw [sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub]
  rw [show (2 * Complex.I : ℂ) = Complex.I + Complex.I from by ring]
  rw [add_smul]
  abel

/-! ## Sublattice axis squared as conjTranspose product -/

/-- `(Ŝ_A^(1))² = (Ŝ_A^(1))ᴴ * Ŝ_A^(1)`. Direct from Hermiticity. -/
theorem sublatticeSpinSOp1_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A =
      (sublatticeSpinSOp1 N A).conjTranspose * sublatticeSpinSOp1 N A := by
  rw [(sublatticeSpinSOp1_isHermitian N A).eq]

theorem sublatticeSpinSOp2_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A =
      (sublatticeSpinSOp2 N A).conjTranspose * sublatticeSpinSOp2 N A := by
  rw [(sublatticeSpinSOp2_isHermitian N A).eq]

theorem sublatticeSpinSOp3_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A =
      (sublatticeSpinSOp3 N A).conjTranspose * sublatticeSpinSOp3 N A := by
  rw [(sublatticeSpinSOp3_isHermitian N A).eq]


end LatticeSystem.Quantum
